"""regime_probe.py -- which hub regime is extremal for the k=10 branch?

Search the k=10 family at fixed r with one hub's norm FIXED at lambda
(t2 = lambda) and the other hub free; report the best R found.
Also: both-free (baseline) and merged (t1=t2) for comparison.

Purpose: if the far-out regime (lambda -> 1-r) is clearly worse than the
central regime, the exclusion argument only needs the central regime.
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "finite-reduction" / "py"))
import k10_feas as K  # noqa: E402

OUT = HERE.parent / "evidence"


def make_centers_fixed(p, r, t2):
    """p = [alpha(10), phi(9), t1, psi1, psi2]; hub2 norm fixed = t2."""
    C = K.make_centers(np.concatenate([p, [0.0, 0.0]])[:23] if False else p, r, 1.0)
    # rebuild explicitly
    al = np.asarray(p[0:10], float)
    ph = np.concatenate([[0.0], np.asarray(p[10:19], float)])
    t1 = float(np.clip(p[19], 0.0, 1.0 - r))
    ps1, ps2 = float(p[20]), float(p[21])
    rho = np.array([K.rho_minus(a, r) for a in al])
    C = np.empty((12, 2))
    C[:10, 0] = rho * np.cos(ph)
    C[:10, 1] = rho * np.sin(ph)
    C[10] = t1 * np.array([math.cos(ps1), math.sin(ps1)])
    C[11] = t2 * np.array([math.cos(ps2), math.sin(ps2)])
    return C


def obj(p, r, t2):
    C = make_centers_fixed(p, r, t2)
    return K.R_cand(C)[0]


def rand_start(r, t2, rng, kind):
    ph = np.linspace(0, 2 * math.pi, 11)[:-1] + rng.normal(0, 0.1, 10)
    ph = ph - ph[0]
    al = np.full(10, math.pi / 10.0) + rng.normal(0, 0.05, 10)
    al = np.clip(al, 0, math.asin(r))
    t1 = rng.uniform(0, min(0.25, 1 - r)) if kind != "free" else rng.uniform(0, 1 - r)
    ps1 = rng.uniform(0, 2 * math.pi)
    ps2 = rng.uniform(0, 2 * math.pi)
    return np.concatenate([al, ph[1:], [t1], [ps1], [ps2]])


def run(r, t2, restarts=14, maxfev=5000, seed=7):
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    t0 = time.time()
    for it in range(restarts):
        kind = "central" if (it % 3) else "free"
        p0 = rand_start(r, t2, rng, kind)
        res = minimize(obj, p0, args=(r, t2), method="Nelder-Mead",
                       options=dict(maxfev=maxfev, xatol=1e-10, fatol=1e-12,
                                    adaptive=True))
        if res.fun < best[0]:
            best = (float(res.fun), res.x.copy())
    C = make_centers_fixed(best[1], r, t2)
    act, nrm = K.active_info(C, r)
    return dict(r=r, t2=t2, R_best=best[0], gap_to_U=best[0] - K.U,
                gap_to_r=best[0] - r, t1=float(best[1][19]),
                n_active=int(act.sum()), norms=nrm.tolist(),
                secs=time.time() - t0, params=best[1].tolist())


def main():
    r = K.U
    rows = []
    for t2 in [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.55, 0.6, 1.0 - r - 1e-6]:
        row = run(r, t2)
        rows.append(row)
        print("t2=%.6f  R_best=%.9f  R-U=%+.6f  t1=%.4f  nact=%d  %.0fs"
              % (t2, row["R_best"], row["gap_to_U"], row["t1"],
                 row["n_active"], row["secs"]), flush=True)
    json.dump(rows, open(OUT / "regime_probe.json", "w"), indent=1)


if __name__ == "__main__":
    main()
