"""r20-chain: THE TWO-ROOT (p+,p-) WHOLE-CHAIN REPRESENTATION of the hub domain.

Setting: two ring centres c_i, c_j with d = |c_i - c_j| = 2a <= 2r (so they can be served by one
hub), midpoint m = (c_i+c_j)/2, unit normal n (choose either sign),
    k = sqrt(r^2 - a^2),     p_+ = m + k n,      p_- = m - k n.
p_+ and p_- are the two centres of radius-r circles through c_i and c_j.

CLAIM (factorisation; verified numerically below, with the sign convention stated carefully):
    rho := circumradius(c_i, c_j, h)  satisfies
        4 a^2 (rho^2 - r^2) = rho^2 * ( |h-p_+|^2 - r^2 ) * ( |h-p_-|^2 - r^2 ) / r^2   ... (algebra)
    hence, for h NOT on the line c_i c_j (where rho = infinity),
        rho <= r     <=>    exactly one of   |h-p_+| <= r ,  |h-p_-| <= r   holds.
    The hub must be on the side of the chord that contains the arc c_i c_j it serves, i.e.
        |h - p_inner| <= r     AND     |h - p_outer| >= r
    where p_inner is the root on the hub's side of the line c_i c_j.

WHOLE-CHAIN DOMAIN: for the chain c_{k}, c_{k+1}, ..., c_{l} the hub must satisfy, for EVERY
consecutive pair,
        |h - p_j^{in}| <= r        (a DISK constraint),  and
        |h - p_j^{out}| >= r       (the complement of a disk).
The inner constraints alone give a convex domain (intersection of disks).  The lead's question:
is the outer constraint AUTOMATIC, i.e. is D(p_j^{out}, r) ∩ B(0,1-r) = EMPTY for all chains in
the legal domain?  If yes the whole-chain hub domain collapses to a convex disk intersection.
This file: (1) verifies the factorisation; (2) computes the p_+- for the certified candidate;
(3) searches for a counterexample to the outer exclusion over the legal domain.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def circumradius(A, B, C):
    e = [np.linalg.norm(B - C), np.linalg.norm(A - C), np.linalg.norm(A - B)]
    if min(e) < 1e-14:
        return np.inf
    ar = abs((B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0])) / 2
    if ar < 1e-15:
        return np.inf
    return e[0] * e[1] * e[2] / (4 * ar)


def roots(ci, cj, r):
    """Return (a, m, n, k, p_plus, p_minus)."""
    ci = np.asarray(ci, float); cj = np.asarray(cj, float)
    d = float(np.linalg.norm(cj - ci))
    a = d / 2
    m = (ci + cj) / 2
    u = (cj - ci) / d
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(r * r - a * a, 0.0)))
    return a, m, n, k, m + k * n, m - k * n


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}; ring order " + ", ".join(map(str, ring_ids)))

    P("\n=== (1) factorisation check: rho<=r <=> exactly one of |h-p_+-|<=r ===")
    rng = np.random.default_rng(5)
    ncase = 0
    bad = 0
    for _ in range(20000):
        r = rng.uniform(0.3, 0.45)
        a = rng.uniform(0.05, r * 0.999)
        th = rng.uniform(0, 2 * PI)
        ph = rng.uniform(0, 2 * PI)
        m = rng.uniform(0, 0.6) * np.array([np.cos(ph), np.sin(ph)])
        u = np.array([np.cos(th), np.sin(th)])
        n = np.array([-u[1], u[0]])
        ci, cj = m - a * u, m + a * u
        _, _, _, k, pp, pm = roots(ci, cj, r)
        h = rng.uniform(-1, 1, 2)
        rho = circumradius(ci, cj, h)
        din = np.linalg.norm(h - pp) <= r
        dout = np.linalg.norm(h - pm) <= r
        pred = (din != dout)
        got = (rho <= r + 1e-12)
        ncase += 1
        if pred != got:
            bad += 1
            if bad < 5:
                P(f"  MISMATCH r={r:.6f} rho={rho:.6f} |h-p+|={np.linalg.norm(h-pp):.6f}"
                  f" |h-p-|={np.linalg.norm(h-pm):.6f} pred={pred} got={got}")
    P(f"  cases={ncase}  mismatches={bad}")

    P("\n=== (2) roots and hub side for the certified candidate ===")
    order = list(range(9))
    for H, lab, chain in ((HA, "A", order[0:4]), (HB, "B", order[4:8])):
        P(f"\n  hub {lab} |H|={np.linalg.norm(H):.9f}")
        for kk in range(len(chain) - 1):
            i, j = chain[kk], chain[kk + 1]
            a, m, n, k, pp, pm = roots(ring[i], ring[j], R)
            dp = float(np.linalg.norm(H - pp)); dm = float(np.linalg.norm(H - pm))
            inner, outer = (pp, pm) if dp < dm else (pm, pp)
            di = float(np.linalg.norm(H - inner)); do = float(np.linalg.norm(H - outer))
            P(f"   ({ring_ids[i]:>2d},{ring_ids[j]:>2d}): a={a:.6f} k={k:.6f}"
              f"  d(H,p+)={dp:.6f} d(H,p-)={dm:.6f}")
            P(f"        inner root p_in={np.round(inner,6)}: |H-p_in|={di:.9f} <= r? {di <= R}"
              f"  (r-| |={R-di:+.3e})")
            P(f"        outer root p_out={np.round(outer,6)}: |H-p_out|={do:.9f} >= r? {do >= R}"
              f"  (| |-r={do-R:+.3e})   |p_out|={np.linalg.norm(outer):.6f}"
              f"   r-|p_out|={R-np.linalg.norm(outer):+.6f}")

    P("\n=== (3) outer exclusion search: is D(p_out,r) ∩ B(0,1-r) always empty? ===")
    P("  (a counterexample needs |p_out| > r, i.e. a radius-r disk through c_i,c_j whose OTHER")
    P("   centre lies outside the unit disk of radius r... we test |p_out| vs r directly)")
    rng = np.random.default_rng(17)
    worst = -1e9
    worst_case = None
    cnt = 0
    nviol = 0
    for trial in range(40000):
        r = rng.uniform(0.34, 0.42)
        # legal: all nine ring centres in B(0,1-r).. actually with |c| >= 1-r for essential
        th = np.sort(rng.uniform(0, 2 * PI, 9))
        rho_ = np.sqrt(rng.uniform((1 - r) ** 2, 1.0, 9))
        rring = np.stack([rho_ * np.cos(th), rho_ * np.sin(th)], 1)
        for k in rng.choice(8, size=4, replace=False):
            ci, cj = rring[k], rring[k + 1]
            a, m, n, kk, pp, pm = roots(ci, cj, r)
            for p in (pp, pm):
                cnt += 1
                # the outer root is the one with the larger |p| (farther from the origin)
                val = np.linalg.norm(p) - r
                if val > worst:
                    worst, worst_case = val, (r, ci.copy(), cj.copy(), p.copy())
                if val > 0:
                    nviol += 1
    P(f"  tested {cnt} root pairs over 40000 random configs")
    P(f"  max (|p| - r) over both roots = {worst:+.6f}   violations (|p|>r) = {nviol}")
    if worst_case is not None:
        P(f"  worst case: r={worst_case[0]:.6f} ci={np.round(worst_case[1],6)}"
          f" cj={np.round(worst_case[2],6)} p={np.round(worst_case[3],6)}")

    P("\n=== (3b) the right question: can a LEGAL HUB lie in the outer disk? ===")
    P("  hub must satisfy |h| <= 1-r; a legal h in D(p_out,r) would mean the hub is on the WRONG")
    P("  side; but if |p_out| - r > (1-r), no legal hub can be in that disk at all.")
    rng = np.random.default_rng(29)
    worst = -1e9
    for trial in range(40000):
        r = rng.uniform(0.34, 0.42)
        th = np.sort(rng.uniform(0, 2 * PI, 9))
        rho_ = np.sqrt(rng.uniform((1 - r) ** 2, 1.0, 9))
        rring = np.stack([rho_ * np.cos(th), rho_ * np.sin(th)], 1)
        for k in range(8):
            ci, cj = rring[k], rring[k + 1]
            a, m, n, kk, pp, pm = roots(ci, cj, r)
            for p in (pp, pm):
                # distance from the origin to the FAR side of D(p,r): |p| - r;  the legal hub
                # region is B(0,1-r); D(p,r) ∩ B(0,1-r) = empty  iff  |p| - r > 1 - r  i.e. |p|>1
                val = np.linalg.norm(p) - 1.0
                worst = max(worst, val)
    P(f"  max over all roots of (|p| - 1) = {worst:+.6f}")
    P("  (negative => every radius-r circle through any legal consecutive pair has BOTH of its")
    P("   centres inside the UNIT circle, so no legal hub (|h|<=1-r) is ever in the outer disk)")
    P("  NOTE: this is the right criterion only if the two roots are the two sides' centres;")
    P("  the quantity that matters is min over roots |p| vs 1-r.")

    (OUT / "two_root.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "two_root.txt"))


if __name__ == "__main__":
    main()
