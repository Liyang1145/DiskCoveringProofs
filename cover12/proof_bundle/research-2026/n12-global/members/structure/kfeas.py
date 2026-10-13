"""n12 -- numerical feasibility of covers by 12 equal disks, by boundary-active count k.

Object: D = closed unit disk.  12 labelled centers in R^2, radius r.
R(C) = max_{x in D} min_i |x - c_i| ; cover at radius r  <=>  R(C) <= r.
k = #{i : |c_i| + r >= 1}  (boundary-active disks).

Purpose: for each prescribed structure (k ring disks + m = 12-k hub disks)
find the minimal r that admits a cover, and report the binding geometry.
This is an EXPLORATORY instrument: it produces candidates and upper bounds,
never a lower bound proof.

Run:  py -3 kfeas.py <mode>
"""
import json
import sys
import numpy as np
from scipy.optimize import minimize


# ---------------------------------------------------------------- grids
def polar_grid(nr=90, nphi=288):
    rho = np.linspace(0.0, 1.0, nr)
    phi = np.linspace(0.0, 2.0 * np.pi, nphi, endpoint=False)
    R, P = np.meshgrid(rho, phi, indexing="ij")
    X = np.stack([R * np.cos(P), R * np.sin(P)], axis=-1).reshape(-1, 2)
    return np.ascontiguousarray(X)


def boundary_grid(nphi=4096):
    phi = np.linspace(0.0, 2.0 * np.pi, nphi, endpoint=False)
    return np.stack([np.cos(phi), np.sin(phi)], axis=-1)


# ------------------------------------------------------- soft min / max
def _softmin(C, X, gamma):
    D = np.linalg.norm(X[:, None, :] - C[None, :, :], axis=2)
    return -(np.log(np.exp(-gamma * D).sum(axis=1))) / gamma, D


def _loss(C, X, beta, gamma):
    m, _ = _softmin(C, X, gamma)
    mx = m.max()
    w = np.exp(beta * (m - mx))
    return mx + np.log(w.sum()) / beta


def hard_R(C, X):
    """exact max over sample set of nearest-center distance."""
    D = np.linalg.norm(X[:, None, :] - C[None, :, :], axis=2)
    m = D.min(axis=1)
    i = int(np.argmax(m))
    return float(m[i]), X[i].copy(), int(np.argmin(D[i]))


def classify_k(C, r, tol=1e-9):
    return int(np.sum(np.linalg.norm(C, axis=1) + r >= 1.0 - tol))


# ------------------------------------------------------------ optimizer
def solve(C0, X, betas=(30.0, 100.0, 300.0, 1000.0), gamma=400.0, maxiter=400):
    C = C0.copy()
    for beta in betas:
        res = minimize(
            _loss, C.ravel(), args=(X, beta, gamma), method="L-BFGS-B",
            options=dict(maxiter=maxiter, maxfun=maxiter * 4, ftol=1e-14, gtol=1e-12),
        )
        C = res.x.reshape(-1, 2)
    return C


# ---------------------------------------------------------- initializers
def init_even(k, r, phase=0.0, t=None, hubs=None, hub_rng=0.0):
    """k ring disks at equal spacing radius t, m hubs at given positions."""
    m = 12 - k
    if t is None:
        t = 0.5 * (1.0 - r + np.sqrt(max(1e-12, 1.0 - r * r)))
    ang = phase + 2.0 * np.pi * np.arange(k) / k
    ring = np.stack([t * np.cos(ang), t * np.sin(ang)], axis=-1)
    if hubs is None:
        if m == 1:
            hubs = np.zeros((1, 2))
        else:
            ha = 2.0 * np.pi * np.arange(m) / m
            hubs = np.stack([hub_rng * np.cos(ha), hub_rng * np.sin(ha)], axis=-1)
    return np.vstack([ring, hubs])


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "calib"
    X = polar_grid(90, 288)
    out = {}

    if mode == "calib":
        # reproduce a 9+3 configuration family; report R for given centers
        cfg = json.load(open(sys.argv[2], encoding="utf-8"))
        C = np.array([[float(a), float(b)] for a, b in cfg["centers_dec17"]])
        Xf = polar_grid(400, 1440)
        R, xstar, i = hard_R(C, Xf)
        out = dict(mode="calib", cfg=sys.argv[2], R_max=R, xstar=xstar.tolist(),
                   nearest=int(i), k=classify_k(C, R),
                   norms=np.linalg.norm(C, axis=1).tolist())
        print(json.dumps(out, indent=1))
        return

    if mode == "even":
        # minimal r for evenly spaced ring + centred hubs (analytic-ish check)
        for k in (9, 10, 11, 12):
            rows = []
            for r in np.arange(0.34, 0.40, 0.002):
                C = init_even(k, r, hub_rng=0.0)
                C = solve(C, X, betas=(60.0, 300.0, 1500.0), maxiter=200)
                R, xs, i = hard_R(C, X)
                rows.append((round(float(r), 4), round(R, 6), classify_k(C, R)))
            out[f"k{k}"] = rows
        print(json.dumps(out, indent=1))
        return

    if mode == "free":
        # free optimisation from several structured starts
        rng = np.random.default_rng(12345)
        Xf = polar_grid(400, 1440)
        for k in (9, 10, 11):
            best = None
            for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 6):
                r0 = {9: 0.361, 10: 0.360, 11: 0.373}[k]
                C0 = init_even(k, r0, phase=0.0,
                               hub_rng=0.0 if trial == 0 else 0.05)
                if trial > 0:
                    C0 = C0 + rng.normal(0, 0.01 * trial, C0.shape)
                C = solve(C0, X, betas=(60.0, 300.0, 1500.0, 6000.0), maxiter=400)
                R, xs, i = hard_R(C, Xf)
                if best is None or R < best[0]:
                    best = (R, C.copy(), xs, classify_k(C, R))
            out[f"k{k}"] = dict(R=best[0], xstar=best[2].tolist(),
                                k_eff=best[3],
                                centers=best[1].tolist(),
                                norms=np.linalg.norm(best[1], axis=1).tolist())
        print(json.dumps(out, indent=1))
        return

    print("unknown mode", mode)


if __name__ == "__main__":
    main()
