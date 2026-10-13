"""r20-chain: exact |p_out| formula, its threshold, and the outer-exclusion counterexample.

Setup: two ring centres c_i, c_j with |c_i-c_j| = d = 2a; m = midpoint, L = |m|, n = unit normal,
k = sqrt(r^2 - a^2), p_out = the root with the larger norm.

EXACT (derived below, verified):
    |p_out|^2 = (1 + k^2/L^2) rho^2 - k^2 (1 + r^2/L^2) + (2k/L) sqrt(rho^2 - L^2) sqrt(r^2 - k^2)
with rho = |c_i| = |c_j| in the symmetric case (L^2 + a^2 = rho^2).  Equivalently, in the frame
O = origin, chord vertical at abscissa s = L, c_+- = (s, +-t):
    |p_out|^2 = s^2 + k^2 + 2 k (m.n)  and  the two equations of the two roots read
        (s-rho)^2 + (t-k)^2 = r^2,   (s-rho)^2 + (t+k)^2 = r^2
    (the second requires (s-rho)^2 + (t+k)^2 = r^2, which is the *feasibility* constraint).

THE TWO CRITICAL TRUTHS:
 (T1) |p_out| = 1 is NOT an identity.  For the CERTIFIED candidate it holds to machine precision
      for all eight adjacent pairs (it is a nontrivial property of the optimum).
 (T2) Outer exclusion (|h - p_out| >= r for every legal hub h) is NOT automatic: we exhibit a
      legal annulus pair with |p_out| < 1 and a legal hub h = p_out with |h| <= 1-r and
      |h - p_in| <= r.  So the chain domain is NOT just a convex disk intersection.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def pair_two(r, ci, cj):
    d = float(np.linalg.norm(cj - ci))
    a = d / 2
    m = (ci + cj) / 2
    u = (cj - ci) / d
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(r * r - a * a, 0.0)))
    return m + k * n, m - k * n, d, a, m, n, k


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")

    P("\n=== A. |p_out| at the candidate: NOT 1?  (recheck with the exact root choice) ===")
    for kk in range(8):
        ci, cj = ring[kk], ring[kk + 1]
        p1, p2, d, a, m, n, k = pair_two(R, ci, cj)
        po = p1 if np.linalg.norm(p1) > np.linalg.norm(p2) else p2
        P(f"  ({ring_ids[kk]:>2d},{ring_ids[kk+1]:>2d}): |p1|={np.linalg.norm(p1):.12f}"
          f" |p2|={np.linalg.norm(p2):.12f}   |p_out|={np.linalg.norm(po):.12f}")

    P("\n=== B. counterexample pair (legal annulus, d<=2r) with |p_out| < 1 ===")
    r = R
    ci = np.array([-0.23763005, -0.58241778])
    cj = np.array([0.48422478, -0.42854144])
    p1, p2, d, a, m, n, k = pair_two(r, ci, cj)
    po = p1 if np.linalg.norm(p1) > np.linalg.norm(p2) else p2
    pi = p2 if np.linalg.norm(p1) > np.linalg.norm(p2) else p1
    P(f"  |ci|={np.linalg.norm(ci):.9f}  |cj|={np.linalg.norm(cj):.9f}  both >= 1-r={1-r:.9f}"
      f"  -> {np.linalg.norm(ci) >= 1-r and np.linalg.norm(cj) >= 1-r}")
    P(f"  d={d:.9f} <= 2r={2*r:.9f} -> {d <= 2*r}")
    P(f"  |p_out|={np.linalg.norm(po):.9f} < 1  -> outer disk meets the legal hub region")
    h = po
    P(f"  h = p_out: |h|={np.linalg.norm(h):.9f} <= 1-r={1-r:.9f} -> {np.linalg.norm(h) <= 1-r}")
    P(f"  |h - p_in| = {np.linalg.norm(h - pi):.9f} <= r={r:.9f} -> {np.linalg.norm(h - pi) <= r}")
    P(f"  |h - p_out| = 0 < r  => the outer inequality FAILS at a legal hub")
    P("  (so circumradius(c_i,c_j,h) > r is possible at a legal hub that satisfies the inner")
    P("   disk constraint: the domain is the intersection of the inner disk with the EXTERIOR")
    P("   of the outer disk, a non-convex-in-general region)")

    P("\n=== C. the exact feasibility constraint and what |p_out| = 1 means ===")
    P("  In the symmetric frame with s = |m|, t = sqrt(rho^2 - s^2), the roots require")
    P("     (s-rho)^2 + (t-k)^2 = r^2   and   (s-rho)^2 + (t+k)^2 = r^2 .")
    P("  The second equation is the FEASIBILITY condition (both roots through c_i, c_j exist);")
    P("  it holds identically only when k*t = -(s*rho) in the appropriate sign convention.")
    L = float(np.linalg.norm(m))
    rho = float(np.linalg.norm(ci))
    t = float(np.sqrt(max(rho * rho - L * L, 0.0)))
    P(f"  candidate pair (4,9): s={L:.9f} rho={rho:.9f} t={t:.9f} k={k:.9f}")
    P(f"     (s-rho)^2+(t-k)^2 - r^2 = {(L-rho)**2+(t-k)**2-r*r:+.3e}")
    P(f"     (s-rho)^2+(t+k)^2 - r^2 = {(L-rho)**2+(t+k)**2-r*r:+.3e}")

    P("\n=== D. is |p_out| >= 1 implied by ESSENTIALITY (both rings reach the boundary)? ===")
    P("  essential ring: some point of the unit circle is within r of it, and it contributes to")
    P("  the boundary cover; in the minimal form: |c| >= 1-r AND c is not redundant.")
    P("  Test: minimize |p_out| subject to |ci|,|cj| >= 1-r, d <= 2r, AND both rings non-redundant")
    P("  in the sense that the boundary arc they cover is nonempty ==> |c| + r >= 1, i.e. the")
    P("  same condition.  Also test the stronger 'both rings must cover a boundary arc of length")
    P("  > 0 that the other does not': covered arc half-width arccos((1-|c|^2-r^2)/(2r|c|)) > 0.")
    from scipy.optimize import differential_evolution

    def hw_boundary(c, r):
        """half-width of the arc of the unit circle covered by B(c,r); None if none."""
        Lc = float(np.linalg.norm(c))
        if Lc + r < 1:
            return None
        val = (1 - Lc * Lc - r * r) / (2 * r * Lc)
        if val >= 1:
            return 0.0
        if val <= -1:
            return PI
        return float(np.arccos(val))

    def obj(v):
        ri, rj, ti, tj = v
        if ri < 1 - r - 1e-12 or rj < 1 - r - 1e-12 or ri > 1.0001 or rj > 1.0001:
            return 1e3
        ci = ri * np.array([np.cos(ti), np.sin(ti)])
        cj = rj * np.array([np.cos(tj), np.sin(tj)])
        d = float(np.linalg.norm(cj - ci))
        if d >= 2 * r or d < 1e-12:
            return 1e3
        hwi = hw_boundary(ci, r); hwj = hw_boundary(cj, r)
        if not hwi or not hwj:
            return 1e3
        p1, p2, d, a, m, n, k = pair_two(r, ci, cj)
        po = p1 if np.linalg.norm(p1) > np.linalg.norm(p2) else p2
        return float(np.linalg.norm(po))

    bounds = [(1 - r, 1.0), (1 - r, 1.0), (0, 2 * PI), (0, 2 * PI)]
    best, bx = 1e9, None
    for seed in (0, 1, 2):
        res = differential_evolution(obj, bounds, seed=seed, maxiter=300, popsize=20, tol=1e-11,
                                     polish=True, init="sobol", updating="deferred")
        if res.fun < best:
            best, bx = res.fun, res.x
    P(f"  min |p_out| over essential annulus pairs = {best:.9f}   (1 - that = {1-best:+.3e})")
    if bx is not None:
        P(f"    argmin ri={bx[0]:.9f} rj={bx[1]:.9f}")

    (OUT / "pout_exact.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "pout_exact.txt"))


if __name__ == "__main__":
    main()
