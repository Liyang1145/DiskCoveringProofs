"""r20-chain: CORRECTED outer-exclusion test (two-root factorisation is off-line only).

The two-root factorisation
    rho(c_i,c_j,h) <= r  <=>  exactly one of |h-p_in| <= r, |h-p_out| <= r
holds for h NOT on the radical line of the pair (for h ON the line both disks contain h or
neither, and rho > r by the strictness).  The hub is always off the line (the chord is not
collinear with the hub), so what matters is:

    OUTER EXCLUSION for the pair  <=>  B(0, 1-r) \\ radical-line  is disjoint from B(p_out, r).

Because p_in and p_out are mirror images across the radical line, and |p_in - p_out| = 2k, the
half-space decomposition gives the clean necessary-and-sufficient condition

    max_{|h| <= 1-r} ( |h - p_out| ) >= r     vs.    min over the *allowed side*.

Since the legal hub region is the disk B(0,1-r) and the "wrong side" of the radical line is a
half-plane, the closest point of B(0,1-r) ∩ {wrong side} to p_out can be computed exactly.
Here we evaluate it numerically for the counterexample pair and scan for a genuine violation.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT
from scipy.optimize import minimize

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
    return (p1, p2, d, a, m, n, k) if np.linalg.norm(p1) > np.linalg.norm(p2) \
        else (p2, p1, d, a, m, n, k)      # p_out, p_in, ...


def circ(A, B, C):
    e = [np.linalg.norm(B - C), np.linalg.norm(A - C), np.linalg.norm(A - B)]
    ar = abs((B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0])) / 2
    return e[0] * e[1] * e[2] / (4 * ar) if ar > 1e-15 else np.inf


def main():
    C, R, ring_ids = load_certified()
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")

    P("\n=== 1. verify the factorisation off the radical line ===")
    rng = np.random.default_rng(5)
    bad = 0
    tot = 0
    for _ in range(30000):
        r = rng.uniform(0.3, 0.45)
        a = rng.uniform(0.02, r * 0.999)
        th = rng.uniform(0, 2 * PI)
        m = rng.uniform(0, 0.9) * np.array([np.cos(th), np.sin(th)])
        u = np.array([np.cos(th + 0.7), np.sin(th + 0.7)])
        n = np.array([-u[1], u[0]])
        ci, cj = m - a * u, m + a * u
        d = 2 * a
        k = float(np.sqrt(max(r * r - a * a, 0.0)))
        p1, p2 = m + k * n, m - k * n
        h = rng.uniform(-1, 1, 2)
        # signed distance to the radical line (through m, direction u)
        sd = float((h - m) @ n)
        if abs(sd) < 1e-9:
            continue
        tot += 1
        din = np.linalg.norm(h - p1) <= r
        dout = np.linalg.norm(h - p2) <= r
        rho = circ(ci, cj, h)
        if (din != dout) != (rho <= r + 1e-12):
            bad += 1
    P(f"  off-line cases: {tot}, mismatches: {bad}")

    P("\n=== 2. the counterexample pair, corrected account ===")
    r = R
    ci = np.array([-0.23763005, -0.58241778])
    cj = np.array([0.48422478, -0.42854144])
    p_out, p_in, d, a, m, n, k = pair(r, ci, cj)
    P(f"  |ci|={np.linalg.norm(ci):.9f} |cj|={np.linalg.norm(cj):.9f} (>= 1-r={1-r:.9f})"
      f"  d={d:.9f} <= 2r={2*r:.9f}  2k={2*k:.9f}")
    P(f"  |p_in|={np.linalg.norm(p_in):.9f}  |p_out|={np.linalg.norm(p_out):.9f}")
    # the hub must be off the radical line; the closest legal-hub point with a genuine violation
    def viol(h):
        if np.linalg.norm(h) > 1 - r:
            return 1e3
        if np.linalg.norm(h - p_in) > r:
            return 1e3                     # inner constraint must hold for a "would-be" hub
        sd = float((h - m) @ n)
        if abs(sd) < 1e-9:
            return 1e3                     # on the line: excluded
        return float(np.linalg.norm(h - p_out))
    best, bx = 1e9, None
    for _ in range(400):
        h0 = rng.uniform(-(1 - r), 1 - r, 2)
        if np.linalg.norm(h0) > 1 - r:
            continue
        res = minimize(viol, h0, method="Nelder-Mead",
                       options=dict(maxiter=4000, maxfev=8000, xatol=1e-12, fatol=1e-14))
        if res.fun < best:
            best, bx = res.fun, res.x
    P(f"  min over legal hubs with the inner constraint, off the line, of |h-p_out| = {best:.9f}")
    P(f"  r = {r:.9f}   ->  {'VIOLATION (outer fails)' if best < r - 1e-9 else 'no violation'}")
    if bx is not None:
        h = bx
        P(f"     h={np.round(h,9)} |h|={np.linalg.norm(h):.9f}  |h-p_in|={np.linalg.norm(h-p_in):.9f}"
          f"  circumradius(ci,cj,h)={circ(ci,cj,h):.9f}  (r={r:.9f})")

    P("\n=== 3. scan: min over legal hubs (inner ok, off line) of |h-p_out| - r ===")
    P("   r      min(|h-p_out|)   r    difference     verdict")
    for rr in (0.34, 0.36, R, 0.40, 0.45, 0.50):
        worst = 1e9
        for _ in range(3000):
            ri = rng.uniform(1 - rr, 1.0); rj = rng.uniform(1 - rr, 1.0)
            ti, tj = rng.uniform(0, 2 * PI, 2)
            ci_ = ri * np.array([np.cos(ti), np.sin(ti)])
            cj_ = rj * np.array([np.cos(tj), np.sin(tj)])
            dd = float(np.linalg.norm(cj_ - ci_))
            if dd >= 2 * rr or dd < 1e-9:
                continue
            po, pi_, d, a, m, n, k = pair(rr, ci_, cj_)
            v = abs(np.linalg.norm(po) - rr) - (1 - rr)
            worst = min(worst, v) if worst is not None else v
        P(f"  {rr:.4f}   (analytic) min over h of |h-p_out| >= | |p_out| - r | "
          f"= {abs(np.linalg.norm(po)-rr):.6f}  vs r={rr:.6f}")

    (OUT / "outer_corrected.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "outer_corrected.txt"))


if __name__ == "__main__":
    main()
