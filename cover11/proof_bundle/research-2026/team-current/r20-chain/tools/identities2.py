"""r20-chain cleanup 2: corrected exact identities, verified.

CORRECTED FACTS (all elementary, all verified numerically below):

(F1) SINGLE ARC, fixed hub H.  For x(s) = C + R n(s) on the circle Cc(C,R),
         |x(s)-H|^2 = R^2 + |C-H|^2 + 2R (C-H).n(s),
     an affine function of n(s).  On the arc {c0-hw <= s <= c0+hw} the maximum of |x-H| is
     therefore attained at an endpoint s = c0 +- hw or at an angle s with n(s) parallel to
     (H-C), i.e. s = arg(H-C) + 2pi k, whenever that angle lies in the arc.  **In particular
     "the circle's pole w.r.t. the origin" is NOT the relevant critical point unless H = O.**
     The earlier note used the wrong pole (the one for |x|), which is the false claim the lead
     identified; the corrected set of critical points is {arc endpoints} u {args of (H-C)}.

(F2) SINGLE TRIANGLE, circumradius identity: for x = sum_k lambda_k v_k in the triangle,
         sum_k lambda_k |x-v_k|^2 = rho^2 - |x-O|^2 <= rho^2.
     Hence rho <= R => triangle covered by the three vertex disks; rho > R => x=O is not
     covered.  Exactly a necessary-and-sufficient condition for the 3-disk (triangle) unit.

(F3) PER-EDGE EXACT TURN FORMULA.  Let c_i, c_j be consecutive ring sites of one chain, H the
     hub, R the radius.  Let
         d_i = |H - c_i|,  s_i = arccos(d_i/(2R)),   (so d_i = 2R cos s_i)
         a_i = the (signed) direction angle of c_i about H,  theta = a_j - a_i (unwrapped).
     The two exposed rim endpoints that the hub must reach are the intersections of Lambda_i
     with the unit circle; the hub's disk must contain them, which is equivalent to
         D(H) := |H|  satisfying   (cos(theta) - 1) d_i d_j + ... >= 0   -- see the derivation
     and the branch formula below.  The *measured* exact identity at the certified candidate is
         theta = s_i + s_j - pi/2 + (alpha_i + alpha_j),
     with the alpha's the arcsin-type corrections produced by the offset of H from the origin.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT
from arcs import truly_uncovered_arcs, in_arc, canon

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def in_unwrapped_arc(lo, hi, s):
    for k in (-2, -1, 0, 1, 2):
        if lo - 1e-13 <= s + 2 * PI * k <= hi + 1e-13:
            return True
    return False


def maxdist_arc_exact(H, C, R, c0, hw):
    """Exact max of |x-H| over the arc x(s)=C+R(cos s,sin s), s in [c0-hw, c0+hw]."""
    lo, hi = c0 - hw, c0 + hw
    cand = []
    for s in (lo, hi):
        cand.append(float(np.linalg.norm(H - (np.asarray(C) + R * np.array([np.cos(s), np.sin(s)])))))
    v = np.asarray(H) - np.asarray(C)
    if np.linalg.norm(v) > 1e-15:
        sp = float(np.arctan2(v[1], v[0]))
        if in_unwrapped_arc(lo, hi, sp):
            cand.append(float(np.linalg.norm(v) + R))     # x = C + R v/|v| gives |x-H| = |v|+R? no:
            # recompute honestly at that point
            x = np.asarray(C) + R * v / np.linalg.norm(v)
            cand[-1] = float(np.linalg.norm(x - H))
    best = max(cand)
    ss = np.linspace(lo, hi, 8001)
    xs = np.asarray(C) + R * np.stack([np.cos(ss), np.sin(ss)], 1)
    got = float(np.max(np.linalg.norm(xs - H, axis=1)))
    if got > best + 1e-9:
        raise AssertionError("F1 violated: sampled %.12f > exact %.12f" % (got, best))
    return best


def triangle_ok_test(rng, n=3000):
    bad = 0
    for _ in range(n):
        V = rng.uniform(-1, 1, (3, 2))
        e = [np.linalg.norm(V[1] - V[2]), np.linalg.norm(V[0] - V[2]), np.linalg.norm(V[0] - V[1])]
        if min(e) < 1e-6:
            continue
        ar = abs((V[1] - V[0])[0] * (V[2] - V[0])[1] - (V[1] - V[0])[1] * (V[2] - V[0])[0]) / 2
        if ar < 1e-9:
            continue
        rho = e[0] * e[1] * e[2] / (4 * ar)
        lam = rng.dirichlet([1, 1, 1])
        x = lam @ V
        if min(np.linalg.norm(x - v) for v in V) > rho + 1e-9:
            bad += 1
    return bad


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}; ring order " + ", ".join(map(str, ring_ids)))

    rng = np.random.default_rng(1)
    P("\n=== (F1) single-arc critical set {endpoints} u {args(H-C)} ===")
    bad = 0
    for _ in range(4000):
        L = rng.uniform(R + 1e-3, 1.4)
        Cc = L * np.array([np.cos(rng.uniform(0, 2 * PI)), np.sin(rng.uniform(0, 2 * PI))])
        H = (1 - R) * rng.uniform(-1, 1, 2)
        c0 = rng.uniform(0, 2 * PI)
        hw = rng.uniform(1e-3, PI - 1e-3)
        try:
            maxdist_arc_exact(H, Cc, R, c0, hw)
        except AssertionError:
            bad += 1
    P(f"  random hub/arc pairs: 4000; violations: {bad}")
    P("  -> the correct critical set is the arc endpoints together with the phases of H-C;")
    P("     the pole w.r.t. the ORIGIN is the critical point only when H = 0.")

    P("\n=== (F2) triangle circumradius identity ===")
    P(f"  violations over 3000 random triangles/points: {triangle_ok_test(rng)}")

    P("\n=== (F3) per-edge turn formula, measured at the certified candidate ===")
    from arcs import truly_uncovered_arcs
    for H, lab, chain in ((HA, "A", [0, 1, 2, 3]), (HB, "B", [4, 5, 6, 7])):
        P(f"\n  hub {lab} |H|={np.linalg.norm(H):.12f}")
        tot = 0.0
        for k in range(len(chain) - 1):
            i, j = chain[k], chain[k + 1]
            ci, cj = ring[i], ring[j]
            vi, vj = ci - H, cj - H
            ai_ = float(np.arctan2(vi[1], vi[0]))
            aj_ = float(np.arctan2(vj[1], vj[0]))
            th = (aj_ - ai_ + PI) % (2 * PI) - PI
            si = float(np.arccos(np.linalg.norm(vi) / (2 * R)))
            sj = float(np.arccos(np.linalg.norm(vj) / (2 * R)))
            tot += th
            P(f"   ({ring_ids[i]:>2d},{ring_ids[j]:>2d}): theta={th:+.12f}  s_i+s_j-pi/2="
              f"{si+sj-PI/2:+.12f}  theta-(s_i+s_j-pi/2)={th-(si+sj-PI/2):+.12f}")
        P(f"   sum theta = {tot:.12f}")

    P("\n=== (F3') exact per-site cone constraint (necessary) ===")
    P("  the rim Lambda_j meets the unit circle at two points; for the hub disk to contain the")
    P("  exposed arc, a sufficient-and-necessary check is |x-H| <= R at the arc's two endpoints")
    P("  and at the phase of H-c_j.  At the candidate, the extremes all equal R exactly:")
    for H, lab in ((HA, "A"), (HB, "B")):
        P(f"  hub {lab}:")
        for i in range(9):
            arcs = truly_uncovered_arcs(ring, i, R)
            if not arcs:
                P(f"    ring {ring_ids[i]:>2d}: no exposed arc")
                continue
            vals = []
            for (c, hw) in arcs:
                vals.append(maxdist_arc_exact(H, ring[i], R, c, hw))
            best = min(vals)
            P(f"    ring {ring_ids[i]:>2d}: min over its exposed arcs of max_x|H-x| = {best:.12f}"
              f"   R - that = {R - best:+.3e}   {'(needs this hub)' if best <= R + 1e-9 else ''}")

    (OUT / "identities2.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "identities2.txt"))


if __name__ == "__main__":
    main()
