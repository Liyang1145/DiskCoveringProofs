"""uniform_dual.py -- does ONE weight triple (W0,W1,W2) work for the whole hub
domain?  Feasibility LP at fixed ratio t:

  find W (fixed, config-independent) with
      cap(config, ring)  <=  t * req(config)      for all configs and all rings,
      w_j0 >= sum_k (|w_jk| + |v_jk|)             (nonnegativity, sufficient)
then bisect t.  If infeasible even at t = 0.1, the certification needs
configuration-dependent (per-box) weights, as in the n11 36-segment scheme.
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dual2 as D2  # noqa: E402

U = D2.U
OUT = HERE.parent / "evidence"
K = 4
PER = 1 + 2 * K


def beta(t, a):
    if t <= 0:
        return math.pi
    if t + a <= U:
        return math.pi
    if abs(t - a) >= U:
        return 0.0
    return math.acos(max(-1.0, min(1.0, (t * t + a * a - U * U) / (2 * t * a))))


def configs(n_t=8, n_d=3):
    a = 1 - 2 * U
    tmax = 1 - U - 1e-6
    ts = [round(tmax * i / (n_t - 1), 6) for i in range(n_t)]
    extra = [0.15, 0.175, 0.2, 0.225, tmax]
    ts = sorted(set(ts + extra))
    out = []
    for i, t1 in enumerate(ts):
        for t2 in ts[i:]:
            b1, b2 = beta(t1, a), beta(t2, a)
            dmin = max(0.0, 2 * math.pi - b1 - b2)
            cands = {round(dmin, 6), round(math.pi, 6)}
            if dmin < math.pi:
                cands.add(round((dmin + math.pi) / 2, 6))
                cands.add(round(min(math.pi, dmin + 0.25), 6))
            for dl in sorted(cands)[:n_d]:
                if dl > math.pi + 1e-12:
                    continue
                if (t1 + a <= U) or (t2 + a <= U) or (b1 + b2 >= 2 * math.pi - dl - 1e-12):
                    out.append((t1, t2, dl))
    return out


def build_all(cfgs, n_rho=25, n_phi=72):
    rows, reqs = [], []
    for (t1, t2, dl) in cfgs:
        A, req, geo = D2.build(t1, t2, dl, K=K, sincos=True, n_rho=n_rho,
                               n_phi=n_phi, clip_req=False)
        rows.append(A)
        reqs.append(req)
    return rows, reqs


def feasible(rows, reqs, t, ncoef=2 * K):
    """LP: exists W (3 blocks) with cap <= t*req per (config,ring)."""
    nw = 3 * PER
    nvar = nw + 3 * ncoef
    A_ubs, b_ubs = [], []
    for A, req in zip(rows, reqs):
        # (A_row - t*req) . w <= 0   (homogeneous; normalised by req(cfg0).w = 1)
        M = np.zeros((A.shape[0], nvar))
        M[:, 0:nw] = A - t * req[None, :]
        A_ubs.append(M)
        b_ubs.append(np.zeros(A.shape[0]))
    A_ub = np.vstack(A_ubs)
    b_ub = np.concatenate(b_ubs)
    rows2, b2 = [], []
    for j in range(3):
        r = np.zeros(nvar)
        r[j * PER] = -1.0
        for k in range(ncoef):
            r[nw + j * ncoef + k] = 1.0
        rows2.append(r); b2.append(0.0)
        for k in range(ncoef):
            r1 = np.zeros(nvar); r1[j * PER + 1 + k] = 1.0
            r1[nw + j * ncoef + k] = -1.0
            rows2.append(r1); b2.append(0.0)
            r2 = np.zeros(nvar); r2[j * PER + 1 + k] = -1.0
            r2[nw + j * ncoef + k] = -1.0
            rows2.append(r2); b2.append(0.0)
    A_ub = np.vstack([A_ub, np.array(rows2)])
    b_ub = np.concatenate([b_ub, np.array(b2)])
    # normalisation: req(reference config 0) = 1
    A_eq = np.zeros((1, nvar)); A_eq[0, 0:nw] = reqs[0]
    b_eq = np.array([1.0])
    c = np.zeros(nvar)
    bounds = [(0.0, None)] + [(None, None)] * (PER - 1) + \
             [(None, None)] * (2 * PER) + [(0.0, None)] * (3 * ncoef)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds,
                  method="highs")
    return res


def main():
    cfgs = configs()
    print("uniform-dual test: %d hub configs, coarse ring grid 25x72" % len(cfgs))
    rows, reqs = build_all(cfgs)
    lo, hi = 0.090, 0.10
    # first check t = 0.1 (the exact criterion)
    for t in (0.1, 0.098, 0.096, 0.094):
        t0 = time.time()
        res = feasible(rows, reqs, t)
        print("  t=%.4f  feasible=%s  (%.1fs) %s"
              % (t, res.status == 0, time.time() - t0,
                 "" if res.status == 0 else res.message))
        if res.status == 0:
            json.dump(dict(t=t, weights=[res.x[i * PER:(i + 1) * PER].tolist()
                                         for i in range(3)]),
                      open(OUT / ("uniform_dual_t%04d.json" % int(t * 1000)), "w"),
                      indent=1)


if __name__ == "__main__":
    main()
