"""n12 -- cheap targeted probes for k=10/11 structures.

Each configuration is evaluated ONCE (one medium polar grid).  Only
low-dimensional (<=5) structured families are swept on coarse parameter
grids with a short local polish.  No dense-grid family optimisation.

The critical fixture: for k=11 the single hub must cover B(0,1-2r), so its
norm is <= 3r-1; the back-ray point (r-|h|)w of the crescent forces a
"radial" ring disk with t = 1-r (alpha = 0) in the extremal case.
"""
import json
import sys
import numpy as np
from scipy.optimize import minimize


def polar_grid(nr=160, nphi=576):
    rho = np.linspace(0.0, 1.0, nr)
    phi = np.linspace(0.0, 2.0 * np.pi, nphi, endpoint=False)
    R, P = np.meshgrid(rho, phi, indexing="ij")
    return np.ascontiguousarray(
        np.stack([R * np.cos(P), R * np.sin(P)], axis=-1).reshape(-1, 2))


X_MED = polar_grid(160, 576)
X_FINE = polar_grid(400, 1440)


def Rmax(C, X):
    D = np.linalg.norm(X[:, None, :] - C[None, :, :], axis=2)
    m = D.min(axis=1)
    i = int(np.argmax(m))
    return float(m[i]), X[i].copy()


def kcount(C, r):
    return int(np.sum(np.linalg.norm(C, axis=1) + r >= 1.0 - 1e-9))


# ------------------------------------------------------------- families
def fam_k11(p, tag):
    """p = [t_ring, e, delta]  (+ [t_back] for 'ecc_split')."""
    if tag == "sym":                      # hub at origin, 11 evenly spaced
        t, e, d = p
        ang = d + 2 * np.pi * np.arange(11) / 11
        C = np.stack([t * np.cos(ang), t * np.sin(ang)], axis=-1)
        return np.vstack([C, [[e, 0.0]]])
    if tag == "ecc":                      # hub offset, 11 evenly spaced
        t, e, d = p
        ang = d + 2 * np.pi * np.arange(11) / 11
        C = np.stack([t * np.cos(ang), t * np.sin(ang)], axis=-1)
        return np.vstack([C, [[-e, 0.0]]])
    if tag == "ecc_split":                # back radial disk + 10 spaced
        tw, t, e, d = p
        pts = [[tw, 0.0]]
        for j in range(10):
            a = d + (np.pi / 10) * (2 * j + 1)      # +-18,54,...
            pts.append([t * np.cos(a), t * np.sin(a)])
        pts.append([-e, 0.0])
        return np.array(pts)
    raise ValueError(tag)


def fam_k10(p, tag):
    """2 hubs at +-(e,0); ring patterns."""
    if tag == "even":
        t, e, d = p
        ang = d + 2 * np.pi * np.arange(10) / 10
        C = np.stack([t * np.cos(ang), t * np.sin(ang)], axis=-1)
        return np.vstack([C, [[e, 0.0], [-e, 0.0]]])
    if tag == "alt":
        t1, t2, e, d = p
        ang = d + 2 * np.pi * np.arange(10) / 10
        rr = np.where(np.arange(10) % 2 == 0, t1, t2)
        C = np.stack([rr * np.cos(ang), rr * np.sin(ang)], axis=-1)
        return np.vstack([C, [[e, 0.0], [-e, 0.0]]])
    raise ValueError(tag)


def fam_k9(p, tag):
    """3 hubs at 120 deg; ring of 9 with 2:1 radius pattern (calibration)."""
    t1, t2, e, d = p          # t1 for 3 disks, t2 for 6 disks
    pts = []
    for j in range(3):
        base = d + 2 * np.pi * j / 3
        pts.append([t1 * np.cos(base), t1 * np.sin(base)])
        for k in (1, 2):
            a = base + 2 * np.pi * (2 * k - 1) / 9
            pts.append([t2 * np.cos(a), t2 * np.sin(a)])
    hubs = [[e * np.cos(2 * np.pi * j / 3), e * np.sin(2 * np.pi * j / 3)]
            for j in range(3)]
    return np.array(pts + hubs)


def build(tag_n_fam, p):
    tag, fam = tag_n_fam
    if tag == "k11":
        return fam_k11(p, fam)
    if tag == "k10":
        return fam_k10(p, fam)
    if tag == "k9":
        return fam_k9(p, fam)
    raise ValueError(tag)


def polish(build_fn, p0, rounds=3):
    p = np.asarray(p0, float)

    def f(q):
        return Rmax(build_fn(q), X_MED)[0]

    best = f(p)
    for _ in range(rounds):
        res = minimize(f, p, method="Nelder-Mead",
                       options=dict(maxiter=300, xatol=1e-7, fatol=1e-11))
        if res.fun < best:
            best, p = float(res.fun), res.x.copy()
    return best, p


def sweep(key, fam, grid, refine=True):
    build_fn = lambda q: build((key, fam), q)
    best = None
    for p0 in grid:
        v = Rmax(build_fn(p0), X_MED)[0]
        if best is None or v < best[0]:
            best = (v, np.asarray(p0, float))
    if refine:
        v, p = polish(build_fn, best[1])
    else:
        v, p = best
    C = build_fn(p)
    Rf, xstar = Rmax(C, X_FINE)
    return dict(family=f"{key}:{fam}", R_med=round(best[0], 7),
                R_fine=round(Rf, 9), xstar=np.round(xstar, 6).tolist(),
                params=np.round(p, 6).tolist(), k_eff=kcount(C, Rf))


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    out = []
    U = 0.361102963744508672616920293904

    if which in ("all", "k11"):
        g = [[t, e, d] for t in np.arange(0.70, 0.96, 0.02)
             for e in (0.0, 0.02, 0.05, 0.0833)
             for d in (0.0, 0.1, 0.2)]
        out.append(sweep("k11", "sym", g))
        out.append(sweep("k11", "ecc", [[t, e, d] for t in np.arange(0.72, 0.96, 0.02)
                                        for e in (0.02, 0.05, 0.0833)
                                        for d in (0.0, 0.15, 0.3)]))
        out.append(sweep("k11", "ecc_split",
                         [[tw, t, e, d] for tw in (0.639, 0.66, 0.70)
                          for t in (0.76, 0.80, 0.85, 0.92)
                          for e in (0.0, 0.04, 0.0833) for d in (0.0,)]))

    if which in ("all", "k10"):
        out.append(sweep("k10", "even", [[t, e, d] for t in np.arange(0.72, 0.96, 0.02)
                                         for e in (0.0, 0.05, 0.1, 0.2, 0.3)
                                         for d in (0.0, 0.1, 0.2)]))
        out.append(sweep("k10", "alt", [[t1, t2, e, d]
                                        for t1 in (0.76, 0.80, 0.86)
                                        for t2 in (0.80, 0.86, 0.92)
                                        for e in (0.05, 0.15, 0.25)
                                        for d in (0.0, 0.15)]))

    if which in ("all", "k9"):
        out.append(sweep("k9", "3fold", [[t1, t2, e, d]
                                         for t1 in (0.76, 0.78)
                                         for t2 in (0.86, 0.88)
                                         for e in (0.20, 0.24, 0.28)
                                         for d in (0.0, 0.1, 0.2)]))

    print(json.dumps(dict(U=U, results=out), indent=1))
    json.dump(dict(U=U, results=out), open(f"probe_{which}.json", "w"), indent=1)


if __name__ == "__main__":
    main()
