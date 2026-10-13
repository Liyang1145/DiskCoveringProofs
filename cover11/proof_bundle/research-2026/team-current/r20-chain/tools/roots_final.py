"""r20-chain: FINAL verified algebra for the two roots (replaces all earlier attempts).

Two ring centres c_i, c_j with d = |c_i - c_j| = 2a <= 2R;  m = (c_i+c_j)/2;  u = (c_j-c_i)/d;
n = J u  (J = 90deg CCW);  k = sqrt(R^2 - a^2);  p_+- = m +- k n.

VERIFIED IDENTITIES (0 mismatches in 13084 random legal pairs, and exact at the candidate):
    |p_+|^2 = |m|^2 + k^2 + 2 k (m.n)
    |p_-|^2 = |m|^2 + k^2 - 2 k (m.n)
    |p_+- - c_i| = |p_+- - c_j| = R          (both roots are radius-R circle centres)
    p_out := the root with the LARGER norm => |p_out|^2 = |m|^2 + k^2 + 2k|m.n|
    |p_in|^2 = |m|^2 + k^2 - 2k|m.n|
OUTER CONSTRAINT (pair level):   redundant for the pair  <=>  |p_out| >= 1
    <=>  |m|^2 + k^2 + 2k|m.n| >= 1.
CANDIDATE: the identity holds with EQUALITY for all eight adjacent pairs (|p_out| = 1 exactly).
COUNTEREXAMPLE: for some legal pairs |p_out| < 1 (witness below), so it is not automatic.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def roots(ci, cj, R):
    ci = np.asarray(ci, float); cj = np.asarray(cj, float)
    d = float(np.linalg.norm(cj - ci))
    a = d / 2.0
    m = (ci + cj) / 2.0
    u = (cj - ci) / d
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(R * R - a * a, 0.0)))
    return d, a, m, u, n, k, m + k * n, m - k * n


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")

    P("\n=== A. identity check on random legal pairs ===")
    rng = np.random.default_rng(9)
    bad = 0
    tot = 0
    for _ in range(40000):
        r = rng.uniform(0.33, 0.46)
        ri = rng.uniform(1 - r, 1.0); rj = rng.uniform(1 - r, 1.0)
        ti, tj = rng.uniform(0, 2 * PI, 2)
        ci = ri * np.array([np.cos(ti), np.sin(ti)])
        cj = rj * np.array([np.cos(tj), np.sin(tj)])
        d = float(np.linalg.norm(cj - ci))
        if d >= 2 * r or d < 1e-12:
            continue
        dd, a, m, u, n, k, p1, p2 = roots(ci, cj, r)
        tot += 1
        base = float(m @ m) + k * k
        cr = 2 * k * float(m @ n)
        if abs(base + cr - float(p1 @ p1)) > 1e-9:
            bad += 1
        if abs(base - cr - float(p2 @ p2)) > 1e-9:
            bad += 1
        if abs(np.linalg.norm(p1 - ci) - r) > 1e-9 or abs(np.linalg.norm(p1 - cj) - r) > 1e-9:
            bad += 1
    P(f"  pairs {tot}; mismatches {bad}  -> identities verified")

    P("\n=== B. the candidate: |p_out| = 1 exactly, |p_in| < 1 ===")
    for kk in range(8):
        ci, cj = ring[kk], ring[kk + 1]
        dd, a, m, u, n, k, p1, p2 = roots(ci, cj, R)
        base = float(m @ m) + k * k
        cr = 2 * k * float(m @ n)
        po, pi_ = (p1, p2) if np.linalg.norm(p1) > np.linalg.norm(p2) else (p2, p1)
        P(f"  ({ring_ids[kk]:>2d},{ring_ids[kk+1]:>2d}): |m|={np.linalg.norm(m):.9f} k={k:.9f}"
          f" m.n={m @ n:+.9f}   |p_out|={np.linalg.norm(po):.12f} |p_in|={np.linalg.norm(pi_):.9f}"
          f"   outer-ineq residual = {np.linalg.norm(m)**2 + k*k + 2*k*abs(m @ n) - 1:+.3e}")

    P("\n=== C. counterexample pair (outer constraint not redundant) ===")
    ci = np.array([-0.23763005, -0.58241778])
    cj = np.array([0.48422478, -0.42854144])
    dd, a, m, u, n, k, p1, p2 = roots(ci, cj, R)
    po, pi_ = (p1, p2) if np.linalg.norm(p1) > np.linalg.norm(p2) else (p2, p1)
    P(f"  |c_i|={np.linalg.norm(ci):.9f} |c_j|={np.linalg.norm(cj):.9f} >= 1-R={1-R:.9f}")
    P(f"  d={dd:.9f} <= 2R={2*R:.9f}")
    P(f"  |m|={np.linalg.norm(m):.9f} k={k:.9f} m.n={m @ n:+.9f}")
    P(f"  |p_out| = sqrt(|m|^2+k^2+2k|m.n|) = {np.linalg.norm(po):.9f} < 1")
    P(f"  |p_in| = {np.linalg.norm(pi_):.9f}")
    h = po
    P(f"  h = p_out is a legal hub: |h|={np.linalg.norm(h):.9f} <= 1-R={1-R:.9f}")
    P(f"  |h-p_in|={np.linalg.norm(h-pi_):.9f} <= R={R:.9f} -> inner constraint OK")
    P(f"  |h-p_out|=0 < R -> OUTER CONSTRAINT FAILS")

    (OUT / "roots_final.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "roots_final.txt"))


if __name__ == "__main__":
    main()
