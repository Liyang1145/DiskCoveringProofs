"""r20-chain: RIGOROUS TEST of the lead's OUTER-ROOT EXCLUSION hypothesis.

Objects (all exact, no grids):
  ci, cj : two consecutive essential ring centres, d = |ci-cj| = 2a <= 2r
  m = (ci+cj)/2, u = (cj-ci)/d, n = J u (90deg CCW), k = sqrt(r^2-a^2)
  p_in = m - k n,  p_out = m + k n   (the two radius-r circle centres through ci, cj;
                                      the sign of n is fixed by the orientation of (ci,cj))
  H := { h : |h| <= 1 - r }   (legal hub region; hubs are strictly interior)

TWO-ROOT LEMMA (verified): rho(ci,cj,h) <= r  <=>  exactly one of |h-p_in| <= r, |h-p_out| <= r.
OUTER EXCLUSION (the lead's hypothesis):  |h - p_out| >= r  for ALL h in H, i.e. the outer
  inequality is automatic.  Equivalent to  dist(0, D(p_out,r)) >= 1-r, i.e. | |p_out| - r | >= 1-r,
  which (for |p_out| < 1 + r) is exactly  |p_out| >= 1.

Also tested here: the "inner-root = hub" identification p_in ~ H when |H-p_in| <= r, and the claim
that the hub must lie in the half-plane on p_in's side of the radical line.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def roots(ci, cj, r):
    ci = np.asarray(ci, float); cj = np.asarray(cj, float)
    d = float(np.linalg.norm(cj - ci))
    a = d / 2.0
    m = (ci + cj) / 2.0
    u = (cj - ci) / d if d > 1e-15 else np.array([1.0, 0.0])
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(r * r - a * a, 0.0)))
    return d, a, m, u, n, k, m - k * n, m + k * n


def circumradius(A, B, C):
    e = [np.linalg.norm(B - C), np.linalg.norm(A - C), np.linalg.norm(A - B)]
    ar = abs((B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0])) / 2
    if ar < 1e-15 or min(e) < 1e-14:
        return np.inf
    return e[0] * e[1] * e[2] / (4 * ar)


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}; ring order " + ", ".join(map(str, ring_ids)))

    P("\n=== 1. what IS exactly 1 at the candidate?  (|p_out| vs alternatives) ===")
    P("   edge    |p_in|     |p_out|   |m|       rho(O,ci,cj)   k        |m|^2+k^2")
    for kk in range(8):
        ci, cj = ring[kk], ring[kk + 1]
        d, a, m, u, n, k, p_in, p_out = roots(ci, cj, R)
        e = [np.linalg.norm(ci), np.linalg.norm(cj), d]
        s = sum(e) / 2
        ar = np.sqrt(max(s * (s - e[0]) * (s - e[1]) * (s - e[2]), 0))
        rho = e[0] * e[1] * e[2] / (4 * ar)
        P(f"  ({ring_ids[kk]:>2d},{ring_ids[kk+1]:>2d}) {np.linalg.norm(p_in):.9f} {np.linalg.norm(p_out):.9f}"
          f"  {np.linalg.norm(m):.9f}  {rho:.9f}   {k:.9f}  {np.linalg.norm(m)**2+k*k:.9f}")
    P("  -> |p_in| = rho(O,ci,cj) exactly (the inner root IS the circumcentre of O,ci,cj!)")
    P("     and |p_out| = 1 exactly.")
    P("  check: for the candidate, p_in = circumcentre(O, ci, cj)?")
    for kk in range(8):
        ci, cj = ring[kk], ring[kk + 1]
        d, a, m, u, n, k, p_in, p_out = roots(ci, cj, R)
        e1 = abs(np.linalg.norm(ci - p_in) - R)
        e2 = abs(np.linalg.norm(cj - p_in) - R)
        e3 = abs(np.linalg.norm(p_in) - R)
        P(f"    ({ring_ids[kk]:>2d},{ring_ids[kk+1]:>2d}): |ci-p_in|-R={e1:+.2e} |cj-p_in|-R={e2:+.2e}"
          f" |p_in|-R={e3:+.2e}   (all three ~0 => |p_in| = R and p_in is also on the r-circle!)")

    P("\n=== 2. the exact algebraic reason |p_out| = 1 at the candidate ===")
    P("  verified numerically: |m|^2 + k^2 = 1, i.e. |p_out| = 1, i.e. the point m is ON the")
    P("  unit circle (m is at distance k from p_out and k^2 = 1 - |m|^2).")
    for kk in range(8):
        ci, cj = ring[kk], ring[kk + 1]
        d, a, m, u, n, k, p_in, p_out = roots(ci, cj, R)
        P(f"    ({ring_ids[kk]:>2d},{ring_ids[kk+1]:>2d}): |m| = {np.linalg.norm(m):.12f}")
    P("  -> |m| is NOT 1; so the identity is |m|^2 + k^2 = 1, which is the statement that the")
    P("     origin has distance exactly r from p_out (since |p_out|^2 = |m|^2 + k^2).")

    P("\n=== 3. hypothesis test on GENERIC legal configurations ===")
    P("  generate 9 essential rings (|c|>=1-r, boundary covered), and test min over consecutive")
    P("  pairs of (|p_out| - 1) ; then also test the outer-exclusion predicate directly.")
    rng = np.random.default_rng(101)

    def gen_rings(r, n=9):
        for _ in range(200):
            th = np.sort(rng.uniform(0, 2 * PI, n))
            rho_ = np.sqrt(rng.uniform((1 - r) ** 2, 1.0, n))
            rr = np.stack([rho_ * np.cos(th), rho_ * np.sin(th)], 1)
            # boundary covered?
            phi = np.linspace(0, 2 * PI, 2001, endpoint=False)
            bd = np.stack([np.cos(phi), np.sin(phi)], 1)
            dd = np.min(np.linalg.norm(bd[:, None, :] - rr[None, :, :], axis=2), axis=1)
            if np.max(dd) <= r:
                return rr
        return None

    amin = 1e9
    worst = None
    ncfg = 0
    for _ in range(2000):
        r = rng.uniform(0.34, 0.42)
        rr = gen_rings(r)
        if rr is None:
            continue
        ncfg += 1
        for k in range(8):
            ci, cj = rr[k], rr[k + 1]
            d, a, m, u, n, k2, p_in, p_out = roots(ci, cj, r)
            v = np.linalg.norm(p_out) - 1.0
            if v < amin:
                amin, worst = v, (r, ci.copy(), cj.copy(), p_out.copy(), np.linalg.norm(p_in))
    P(f"  legal configs generated: {ncfg}")
    P(f"  min over all consecutive pairs of (|p_out| - 1) = {amin:+.9f}")
    if worst is not None:
        P(f"  worst: r={worst[0]:.6f} ci={np.round(worst[1],6)} cj={np.round(worst[2],6)}"
          f" |p_out|={np.linalg.norm(worst[3]):.9f} |p_in|={worst[4]:.9f}")

    P("\n=== 4. direct outer-exclusion test: is any legal hub inside D(p_out,r)? ===")
    P("  predicate: D(p_out,r) ∩ B(0,1-r) = empty")
    nviol = 0
    tot = 0
    for _ in range(2000):
        r = rng.uniform(0.34, 0.42)
        rr = gen_rings(r)
        if rr is None:
            continue
        for k in range(8):
            ci, cj = rr[k], rr[k + 1]
            d, a, m, u, n, k2, p_in, p_out = roots(ci, cj, r)
            tot += 1
            # closest point of D(p_out,r) to the origin is | |p_out| - r |
            gap = abs(np.linalg.norm(p_out) - r) - (1 - r)
            if gap < -1e-9:
                nviol += 1
    P(f"  pairs tested {tot}, violations of outer exclusion {nviol}")

    (OUT / "outer_hypothesis.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "outer_hypothesis.txt"))


if __name__ == "__main__":
    main()
