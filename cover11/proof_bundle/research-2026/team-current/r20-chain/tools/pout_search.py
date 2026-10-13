"""r20-chain: DIRECT search for the minimum of |p_out| over legal consecutive ring pairs.

Legal pair data:  c_i, c_j with |c_i|,|c_j| in [1-r, 1] (essential annulus), d=|c_i-c_j| <= 2r.
p_in, p_out = m -+ k n  (k = sqrt(r^2 - d^2/4)), p_out := the root with the LARGER |p|.
Outer exclusion holds for a pair iff  D(p_out, r) ∩ B(0, 1-r) = empty, i.e. |p_out| >= 1.

We minimize |p_out| over the pair domain by global search for several r, and also report the
quantity that actually matters: the minimum over legal hubs h of ... equivalently whether the
outer inequality |h - p_out| >= r can fail.
"""
import numpy as np
from scipy.optimize import differential_evolution
from r20geom import OUT

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def pout_of_pair(r, ri, rj, ti, tj):
    ci = ri * np.array([np.cos(ti), np.sin(ti)])
    cj = rj * np.array([np.cos(tj), np.sin(tj)])
    d = float(np.linalg.norm(cj - ci))
    if d >= 2 * r or d < 1e-12:
        return None, None, d
    a = d / 2
    m = (ci + cj) / 2
    u = (cj - ci) / d
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(r * r - a * a, 0.0)))
    p1, p2 = m + k * n, m - k * n
    p_in, p_out = (p1, p2) if np.linalg.norm(p1) < np.linalg.norm(p2) else (p2, p1)
    return p_in, p_out, d


def main():
    P("=== minimize |p_out| over legal consecutive pairs ===")
    P("  variables: ri,rj in [1-r,1], ti,tj in [0,2pi] ; objective |p_out|")
    for r in (0.34, 0.36, 0.37998385311983873, 0.38, 0.40, 0.42, 0.45, 0.412806):
        def obj(v):
            ri, rj, ti, tj = v
            pi, po, d = pout_of_pair(r, ri, rj, ti, tj)
            if po is None:
                return 1e3
            return float(np.linalg.norm(po))
        bounds = [(1 - r, 1.0), (1 - r, 1.0), (0, 2 * np.pi), (0, 2 * np.pi)]
        best = 1e9
        bx = None
        for seed in (0, 1, 2):
            res = differential_evolution(obj, bounds, seed=seed, maxiter=400, popsize=25,
                                         tol=1e-12, mutation=(0.3, 1.2), recombination=0.9,
                                         polish=True, init="sobol", updating="deferred")
            if res.fun < best:
                best, bx = res.fun, res.x
        pi, po, d = pout_of_pair(r, *bx)
        P(f"  r={r:.9f}: min |p_out| = {best:.9f}   (1 - that = {1-best:+.3e})"
          f"   argmin ri={bx[0]:.6f} rj={bx[1]:.6f} d={d:.6f}  |p_in|={np.linalg.norm(pi):.6f}")

    P("\n=== does |p_out| = 1 hold exactly on the boundary of the domain? ===")
    P("  take ri = rj = 1-r (the inner radius of the annulus) and vary the angle spread")
    r = 0.37998385311983873
    for dfrac in (0.2, 0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6, 1.8, 1.99):
        ri = rj = 1 - r
        alpha = dfrac * np.arcsin(min(dfrac * 0 + 1, 1) * 0 + 1) * 0  # placeholder
        # choose the angle between the two points so that d = dfrac * 2r
        d = dfrac * 2 * r
        if d > 2 * ri:
            continue
        # chord of circle radius ri with chord length d
        half = d / 2
        # place symmetric about the x axis, both at radius ri
        x = np.sqrt(max(ri * ri - half * half, 0.0))
        ci = np.array([x, half]); cj = np.array([x, -half])
        pi, po, dd = pout_of_pair(r, ri, ri, 0.0, 0.0)
        # recompute directly
        m = (ci + cj) / 2
        u = (cj - ci) / dd
        n = np.array([-u[1], u[0]])
        k = np.sqrt(max(r * r - (dd / 2) ** 2, 0.0))
        p1, p2 = m + k * n, m - k * n
        po = p1 if np.linalg.norm(p1) > np.linalg.norm(p2) else p2
        pi_ = p2 if np.linalg.norm(p1) > np.linalg.norm(p2) else p1
        P(f"  d/(2r)={dfrac:.2f} d={dd:.6f} ri=rj={ri:.6f} |m|={np.linalg.norm(m):.9f}"
          f"  |p_out|={np.linalg.norm(po):.9f}  |p_in|={np.linalg.norm(pi_):.9f}"
          f"  check |ci-p_out|-r={np.linalg.norm(ci-po)-r:+.3e}")

    P("\n=== interpretation ===")
    P("  if min |p_out| >= 1 then the outer inequality |h-p_out| >= r is automatic for all legal")
    P("  hubs (|h| <= 1-r) and the chain domain collapses to a convex disk intersection.")
    (OUT / "pout_search.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "pout_search.txt"))


if __name__ == "__main__":
    main()
