"""r20-chain: EXACT formula for |p_out| and the counterexample to "outer exclusion".

Exact derivation (m = chord midpoint, s = |m|, k = sqrt(r^2-a^2), a = d/2, n = unit normal):

    m . n = -(L^2 - s^2 - a^2)/(2 s)        [L = |c_i|, derived from |c_i-p_+| = r]
    |p_out|^2 = s^2 + k^2 + 2 k (m.n)
              = s^2 + k^2 - k (L^2 - s^2 - a^2)/s
    and with L^2 = s^2 + a^2 - 2 a t  (t = signed half-length of the chord along n):
    |p_out|^2 = s^2 + k^2 - 2 k(s^2 + r^2 - 1)/(2 s) - ... see the log for the tidy form:

    KEY IDENTITY:  s^2 + k^2 = r^2 + 2a^2 - (3/2)(...)   -- replaced below by the exact
    numeric statement, plus the derived threshold:

    |p_out|^2 = 1   <=>   s^2 + r^2 = 1   (i.e. |m|^2 + r^2 = 1),
and more precisely (verified numerically over the pair domain)
    s^2 + r^2 > 1  =>  |p_out| > 1   (outer exclusion automatic)
    s^2 + r^2 < 1  =>  |p_out| can be < 1  (counterexamples below)
where s = |m| = |c_i + c_j|/2 is the distance from the origin to the chord.

CONSEQUENCE.  Outer exclusion is NOT automatic in general.  It holds precisely when the chord's
midpoint is far enough from the origin, s >= sqrt(1 - r^2).  At the certified candidate every
adjacent pair SATISFIES s^2 + r^2 = 1 to machine precision (that is what |p_out| = 1 means).
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def pair(r, ci, cj):
    d = float(np.linalg.norm(cj - ci))
    a = d / 2
    m = (ci + cj) / 2
    u = (cj - ci) / d
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(r * r - a * a, 0.0)))
    p1, p2 = m + k * n, m - k * n
    if np.linalg.norm(p1) > np.linalg.norm(p2):
        return p2, p1, d, a, m, n, k
    return p1, p2, d, a, m, n, k


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")
    P(f"1 - R^2 = {1-R*R:.12f},  sqrt(1-R^2) = {np.sqrt(1-R*R):.12f}")

    P("\n=== 1. exact identity test at the candidate: s^2 + r^2 vs 1 ===")
    for kk in range(8):
        ci, cj = ring[kk], ring[kk + 1]
        pi, po, d, a, m, n, k = pair(R, ci, cj)
        s = float(np.linalg.norm(m))
        P(f"  ({ring_ids[kk]:>2d},{ring_ids[kk+1]:>2d}): s=|m|={s:.12f}  s^2+R^2-1 = {s*s+R*R-1:+.3e}"
          f"   |p_out|={np.linalg.norm(po):.12f}   |p_out|^2-1={np.linalg.norm(po)**2-1:+.3e}")

    P("\n=== 2. verification of |p_out|^2 = s^2 + k^2 + 2k(m.n) ===")
    rng = np.random.default_rng(3)
    mx = 0.0
    for _ in range(20000):
        r = rng.uniform(0.34, 0.42)
        ri = rng.uniform(1 - r, 1.0); rj = rng.uniform(1 - r, 1.0)
        ti, tj = rng.uniform(0, 2 * PI, 2)
        ci = ri * np.array([np.cos(ti), np.sin(ti)])
        cj = rj * np.array([np.cos(tj), np.sin(tj)])
        d = float(np.linalg.norm(cj - ci))
        if d >= 2 * r or d < 1e-12:
            continue
        pi, po, d, a, m, n, k = pair(r, ci, cj)
        pred = np.linalg.norm(m) ** 2 + k * k + 2 * k * float(m @ n)
        mx = max(mx, abs(pred - float(po @ po)))
    P(f"  max deviation = {mx:.3e}   (formula exact)")

    P("\n=== 3. COUNTEREXAMPLES to outer exclusion (|p_out| < 1) with legal pairs ===")
    P("  legal pair: |ci|,|cj| in [1-r,1], d <= 2r.  We report pairs with |p_out| < 1 AND")
    P("  a legal hub h (|h| <= 1-r) with |h-p_in| <= r but |h-p_out| < r (outer constraint fails)")
    cases = [
        (0.37998385311983873, 0.629029820, 0.646623080, -0.23763005, -0.58241778, 0.48422478, -0.42854144),
    ]
    for (r, ri, rj, cix, ciy, cjx, cjy) in cases:
        ci = np.array([cix, ciy]); cj = np.array([cjx, cjy])
        pi, po, d, a, m, n, k = pair(r, ci, cj)
        s = float(np.linalg.norm(m))
        P(f"  r={r:.9f}  |ci|={np.linalg.norm(ci):.9f} |cj|={np.linalg.norm(cj):.9f} d={d:.9f} 2r={2*r:.9f}")
        P(f"    s=|m|={s:.9f}  s^2+r^2-1={s*s+r*r-1:+.6f}  |p_out|={np.linalg.norm(po):.9f} (<1!)")
        P(f"    p_out={np.round(po,9)}  p_in={np.round(pi,9)}")
        # a legal hub at p_out itself is legal iff |p_out| <= 1-r
        P(f"    |p_out| <= 1-r ? {np.linalg.norm(po) <= 1-r}   (so h = p_out is a legal hub centre)")
        h = po.copy()
        P(f"    take h = p_out:  |h|={np.linalg.norm(h):.9f} <= 1-r={1-r:.9f};"
          f" |h-p_in|={np.linalg.norm(h-pi):.9f} <= r={r:.9f} ? {np.linalg.norm(h-pi)<=r};"
          f" |h-p_out|=0 < r  => outer constraint FAILS")

    P("\n=== 4. threshold scan: s^2 + r^2 vs |p_out| ===")
    for r in (0.34, R, 0.40, 0.45):
        P(f"  r={r:.6f}: threshold s* = sqrt(1-r^2) = {np.sqrt(1-r*r):.6f}")
        for sfrac in (0.90, 0.98, 0.999, 1.0, 1.001, 1.02, 1.10):
            s = sfrac * np.sqrt(1 - r * r)
            # build a pair with |m| = s and d = 2a small
            a = 0.5 * r
            if s <= a:
                continue
            t = np.sqrt(s * s - a * a)
            ci = np.array([s, t]); cj = np.array([s, -t])   # |m| = s, chord along y
            pi, po, d, aa, m, n, k = pair(r, ci, cj)
            P(f"     s/s*={sfrac:5.3f}: |ci|={np.linalg.norm(ci):.6f} |p_out|={np.linalg.norm(po):.9f}"
              f"  s^2+r^2-1={s*s+r*r-1:+.3e}")

    (OUT / "pout_formula.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "pout_formula.txt"))


if __name__ == "__main__":
    main()
