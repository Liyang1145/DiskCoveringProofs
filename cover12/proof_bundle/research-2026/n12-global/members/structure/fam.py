"""n12 -- minimal covering radius within structured families (numeric).

Families are described by an m-fold symmetric hub pattern (m = 12-k) plus a
ring of k boundary-active disks with a periodic radius pattern.  For each
family we minimise R(C) = max_{x in D} min_i |x-c_i| over the family
parameters.  Outputs are EXPLORATORY upper bounds on the family minimum,
never lower-bound proofs.

Run: py -3 fam.py <k> [restarts]
"""
import json
import sys
import numpy as np
from scipy.optimize import minimize


def polar_grid(nr=180, nphi=720):
    rho = np.linspace(0.0, 1.0, nr)
    phi = np.linspace(0.0, 2.0 * np.pi, nphi, endpoint=False)
    R, P = np.meshgrid(rho, phi, indexing="ij")
    return np.ascontiguousarray(
        np.stack([R * np.cos(P), R * np.sin(P)], axis=-1).reshape(-1, 2))


def hard_R(C, X):
    D = np.linalg.norm(X[:, None, :] - C[None, :, :], axis=2)
    m = D.min(axis=1)
    i = int(np.argmax(m))
    return float(m[i]), X[i].copy()


# ------------------------------------------------------------- families
def build(k, p, pattern=None, sym=None):
    """k ring disks + (12-k) hubs.

    p = [t_1..t_s, a, delta]  where s = len(pattern) radii per sector,
    a = hub norm, delta = ring phase.
    pattern: list of per-sector ring radii (None -> single radius),
    sym: rotational symmetry order (default 12-k, or 1).
    """
    m = 12 - k
    if sym is None:
        sym = m if m > 0 else 1
    if pattern is None:
        pattern = [1.0]
    s = len(pattern)
    assert k == sym * s, (k, sym, s)
    radii = np.asarray(p[:s])
    a = p[s]
    delta = p[s + 1]
    sec = 2.0 * np.pi / sym
    pts = []
    for j in range(sym):
        for idx in range(s):
            ang = delta + sec * j + sec * (idx + 0.5) / s
            pts.append([radii[idx] * np.cos(ang), radii[idx] * np.sin(ang)])
    hubs = []
    for j in range(m):
        ha = 0.0 + 2.0 * np.pi * j / m          # hub angle fixed at 0 + 2pi j/m
        hubs.append([a * np.cos(ha), a * np.sin(ha)])
    return np.array(pts + hubs, dtype=float)


def optimize_family(k, pattern, sym=None, starts=None, X=None, verbose=False):
    if X is None:
        X = polar_grid()
    s = len(pattern) if pattern else 1
    m = 12 - k
    best = None
    if starts is None:
        starts = []
        for t in (0.70, 0.75, 0.80, 0.85, 0.92):
            for a in (0.0, 0.02, 0.05, 0.08):
                for d in (0.0, np.pi / 6, np.pi / 12):
                    tt = [t + 0.03 * i for i in range(s)]
                    starts.append(np.array(tt + [a, d]))
    for p0 in starts:
        f = lambda p: hard_R(build(k, p, pattern, sym), X)[0]
        res = minimize(f, np.asarray(p0, float), method="Nelder-Mead",
                       options=dict(maxiter=3000, xatol=1e-9, fatol=1e-12))
        if best is None or res.fun < best[0]:
            best = (float(res.fun), res.x.copy())
        if verbose:
            print("  start", np.round(p0, 3), "->", res.fun, flush=True)
    return best


def main():
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    X = polar_grid(180, 720)
    patterns = {
        9: [[1.0], [1.0, 1.0, 1.0], [1.0, 1.0]],
        10: [[1.0], [1.0, 1.0], [1.0, 1.0, 1.0, 1.0, 1.0]],
        11: [[1.0]],
        12: [[1.0]],
    }
    out = {}
    for pat in patterns[k]:
        sym = k // len(pat)
        r, p = optimize_family(k, pat, sym=sym, X=X)
        C = build(k, p, pat, sym)
        R, xstar = hard_R(C, polar_grid(600, 2400))
        norms = np.linalg.norm(C, axis=1)
        kk = int(np.sum(norms + R >= 1.0 - 1e-9))
        out[f"pat={pat}"] = dict(
            R_grid=round(r, 9), R_fine=round(R, 9), xstar=xstar.tolist(),
            params=p.tolist(), k_eff=kk, norms=[round(v, 6) for v in norms])
        print(f"k={k} pattern={pat}  R_fine={R:.9f}  k_eff={kk}", flush=True)
        print("   params", np.round(p, 6).tolist(), flush=True)
    json.dump(out, open(f"fam_k{k}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
