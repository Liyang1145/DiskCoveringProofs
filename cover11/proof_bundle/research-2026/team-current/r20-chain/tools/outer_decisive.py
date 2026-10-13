"""r20-chain: the DECISIVE test of outer exclusion.

For a consecutive pair (c_i, c_j), d <= 2r:
   p_in, p_out : the two radius-r circle centres through c_i, c_j (p_out = larger |p|)
   legal hub region: |h| <= 1 - r
   inner constraint: |h - p_in| <= r        (needed: circumradius(c_i,c_j,h) <= r)
   outer constraint: |h - p_out| >= r       (the other factor of the two-root factorisation)

OUTER EXCLUSION holds for the pair iff   B(0,1-r) ∩ B(p_in,r) ⊂ R^2 \\ B(p_out,r),
i.e. iff every legal hub that satisfies the inner constraint also satisfies the outer one.
Since |h - p_out| <= |h - p_in| + |p_in - p_out|, a violation needs |p_in - p_out| < 2r.
Here  |p_in - p_out| = 2k = 2 sqrt(r^2 - d^2/4), so a violation needs d > 0 (strictly).

We search: minimize |h - p_out| subject to |h| <= 1-r and |h - p_in| <= r.
Value >= r for all legal pairs => outer exclusion is AUTOMATIC (the chain domain is the
convex disk intersection).  Value < r => a genuine, concretely described counterexample.
"""
import numpy as np
from scipy.optimize import differential_evolution
from r20geom import OUT

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def pair_data(r, ci, cj):
    d = float(np.linalg.norm(cj - ci))
    if d >= 2 * r or d < 1e-12:
        return None
    a = d / 2
    m = (ci + cj) / 2
    u = (cj - ci) / d
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(r * r - a * a, 0.0)))
    p1, p2 = m + k * n, m - k * n
    if np.linalg.norm(p1) > np.linalg.norm(p2):
        return p2, p1, d, k          # p_in, p_out
    return p1, p2, d, k


def main():
    P("=== minimize |h - p_out| over (legal pair, legal hub, inner constraint) ===")
    P("  variables: r, ri, rj, ti, tj, hx, hy  with ri,rj in [1-r,1], |h| <= 1-r,")
    P("  |h - p_in| <= r.   value >= r  =>  outer exclusion automatic for that r.")
    R0 = 0.37998385311983873
    for r in (0.2, 0.25, 1 / 3, R0, 0.40, 0.42, 0.45, 0.48, 0.499):

        def obj(v):
            ri, rj, ti, tj, hx, hy = v
            if ri < 1 - r - 1e-12 or ri > 1 + 1e-12 or rj < 1 - r - 1e-12 or rj > 1 + 1e-12:
                return 1e3
            h = np.array([hx, hy])
            if np.linalg.norm(h) > 1 - r + 1e-12:
                return 1e3
            ci = ri * np.array([np.cos(ti), np.sin(ti)])
            cj = rj * np.array([np.cos(tj), np.sin(tj)])
            pd = pair_data(r, ci, cj)
            if pd is None:
                return 1e3
            p_in, p_out, d, k = pd
            if np.linalg.norm(h - p_in) > r + 1e-12:
                return 1e3
            return float(np.linalg.norm(h - p_out))

        bounds = [(1 - r, 1.0), (1 - r, 1.0), (0, 2 * np.pi), (0, 2 * np.pi),
                  (-(1 - r), 1 - r), (-(1 - r), 1 - r)]
        best = 1e9
        bx = None
        for seed in (0, 1, 2):
            res = differential_evolution(obj, bounds, seed=seed, maxiter=300, popsize=20,
                                         tol=1e-11, polish=True, init="sobol",
                                         updating="deferred")
            if res.fun < best:
                best, bx = res.fun, res.x
        verdict = "AUTOMATIC (>= r)" if best >= r - 1e-9 else "*** VIOLATION FOUND ***"
        P(f"  r={r:.9f}: min |h-p_out| = {best:.9f}   r = {r:.9f}   r - value = {r-best:+.3e}"
          f"   {verdict}")
        if bx is not None and best < r - 1e-9:
            ri, rj, ti, tj, hx, hy = bx
            ci = ri * np.array([np.cos(ti), np.sin(ti)])
            cj = rj * np.array([np.cos(tj), np.sin(tj)])
            p_in, p_out, d, k = pair_data(r, ci, cj)
            h = np.array([hx, hy])
            P(f"      witness: ri={ri:.9f} rj={rj:.9f} d={d:.9f} 2r={2*r:.9f}")
            P(f"      ci={np.round(ci,9)} cj={np.round(cj,9)}  |ci|={np.linalg.norm(ci):.9f}"
              f" |cj|={np.linalg.norm(cj):.9f}")
            P(f"      p_in={np.round(p_in,9)} |p_in|={np.linalg.norm(p_in):.9f}")
            P(f"      p_out={np.round(p_out,9)} |p_out|={np.linalg.norm(p_out):.9f}")
            P(f"      h={np.round(h,9)} |h|={np.linalg.norm(h):.9f} (1-r={1-r:.9f})")
            P(f"      |h-p_in|={np.linalg.norm(h-p_in):.9f} (<= r?)"
              f"  |h-p_out|={np.linalg.norm(h-p_out):.9f} (< r!)")

    (OUT / "outer_decisive.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "outer_decisive.txt"))


if __name__ == "__main__":
    main()
