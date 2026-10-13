"""dual_refine.py -- convergence test of the k=10 dual LP.

Question: at the worst hub configurations found in dual_scan, does m* stay
below 0.1 when (a) the ring grid is refined, (b) the weight degree K grows,
(c) sine terms (phase freedom) are allowed?

If yes -> a dual exists with genuine margin and the remaining obligation is
interval certification.  If no -> the per-ring relaxation of the dual is
insufficient and the aggregation must use the joint covering condition.
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

U = 0.361102963744508672616920293904
OUT = HERE.parent / "evidence"


def wrap(x):
    return (x + math.pi) % (2 * math.pi) - math.pi


def basis_arc(center, half, K, sincos):
    """basis: w(theta) = a0 + sum_k ak cos(k th) [+ bk sin(k th)]."""
    n = 1 + K * (2 if sincos else 1)
    b = np.zeros(n)
    b[0] = 2.0 * half
    for k in range(1, K + 1):
        b[k] = (math.sin(k * (center + half)) - math.sin(k * (center - half))) / k
        if sincos:
            b[K + k] = -(math.cos(k * (center + half)) - math.cos(k * (center - half))) / k
    return b


def basis_arc_int(cA, hA, cB, hB, K, sincos):
    d = wrap(cA - cB)
    lo = max(-hB, d - hA)
    hi = min(hB, d + hA)
    if hi <= lo:
        return np.zeros(1 + K * (2 if sincos else 1))
    c, h = cB + 0.5 * (lo + hi), 0.5 * (hi - lo)
    return basis_arc(c, h, K, sincos)


def build(t1, t2, delta, K, n_rho, n_phi, sincos):
    h1 = np.array([t1, 0.0])
    h2 = t2 * np.array([math.cos(delta), math.sin(delta)])
    d = float(np.hypot(*(h1 - h2)))
    b = math.acos(max(-1.0, min(1.0, d / (2 * U)))) if d > 0 else math.pi / 2
    away1 = math.atan2(*(h1 - h2)[::-1]) if d > 0 else 0.0
    away2 = math.atan2(*(h2 - h1)[::-1]) if d > 0 else math.pi
    E = [(away1, math.pi - b), (away2, math.pi - b)]
    per = 1 + K * (2 if sincos else 1)
    nw = 3 * per
    req = np.zeros(nw)
    req[0:per] = basis_arc(0.0, math.pi, K, sincos)
    for j in (0, 1):
        req[(j + 1) * per:(j + 2) * per] += basis_arc(wrap(E[j][0]), E[j][1], K, sincos)
    rows = []
    for rho in np.linspace(1.0 - U, math.sqrt(1.0 - U * U), n_rho):
        ah = math.acos(max(-1, min(1, (1 + rho * rho - U * U) / (2 * rho))))
        for phi in np.linspace(0, 2 * math.pi, n_phi, endpoint=False):
            c = rho * np.array([math.cos(phi), math.sin(phi)])
            row = np.zeros(nw)
            row[0:per] += basis_arc(phi, ah, K, sincos)
            for j, hj in enumerate((h1, h2)):
                ell = float(np.hypot(*(c - hj)))
                if ell < 2 * U:
                    bet = math.acos(max(-1, min(1, ell / (2 * U))))
                    psi = math.atan2(*(c - hj)[::-1])
                    row[(j + 1) * per:(j + 2) * per] += \
                        basis_arc_int(psi, bet, E[j][0], E[j][1], K, sincos)
            rows.append(row)
    return np.array(rows), req


def solve(t1, t2, delta, K=4, n_rho=22, n_phi=72, sincos=False, neg_tol=1e-9):
    A, req = build(t1, t2, delta, K, n_rho, n_phi, sincos)
    per = A.shape[1] // 3
    nw = A.shape[1]
    nr = A.shape[0]
    # auxiliary variables for the nonnegativity constraints of each weight:
    # with sin terms the sufficient condition is a0 >= sqrt(sum of squares)
    # (we use the linear stronger one a0 >= sum |coef|, as before)
    ncoef = per - 1
    nvar = nw + 3 * ncoef + 1
    mi = nw + 3 * ncoef
    A_ub = np.zeros((nr, nvar))
    A_ub[:, 0:nw] = A
    A_ub[:, mi] = -1.0
    b_ub = np.zeros(nr)
    rows2, b2 = [], []
    for j in range(3):
        r = np.zeros(nvar)
        r[j * per] = -1.0
        for k in range(ncoef):
            r[nw + j * ncoef + k] = 1.0
        rows2.append(r)
        b2.append(0.0)
        for k in range(ncoef):
            r1 = np.zeros(nvar); r1[j * per + 1 + k] = 1.0
            r1[nw + j * ncoef + k] = -1.0
            rows2.append(r1); b2.append(0.0)
            r2 = np.zeros(nvar); r2[j * per + 1 + k] = -1.0
            r2[nw + j * ncoef + k] = -1.0
            rows2.append(r2); b2.append(0.0)
    A_ub = np.vstack([A_ub, np.array(rows2)])
    b_ub = np.concatenate([b_ub, np.array(b2)])
    A_eq = np.zeros((1, nvar)); A_eq[0, 0:nw] = req
    b_eq = np.array([1.0])
    c = np.zeros(nvar); c[mi] = 1.0
    bounds = [(0.0, None)] + [(None, None)] * (per - 1) + \
             [(None, None)] * (2 * per) + [(0.0, None)] * (3 * ncoef) + [(0.0, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds,
                  method="highs")
    return (float(res.fun) if res.status == 0 else None), res.status


def main():
    cfgs = [("worst", 0.16, 0.2307, 2.8256),
            ("worst2", 0.16, 0.16, 2.8256),
            ("extremal", 0.1197, 0.2625, 3.0715),
            ("mid", 0.15, 0.35, 2.6)]
    rows = []
    for name, t1, t2, dl in cfgs:
        for (K, n_rho, n_phi, sc) in [(4, 22, 72, False), (4, 40, 144, False),
                                      (6, 40, 144, False), (4, 40, 144, True),
                                      (6, 40, 144, True), (6, 60, 216, True)]:
            t0 = time.time()
            m, st = solve(t1, t2, dl, K, n_rho, n_phi, sc)
            rows.append(dict(name=name, t1=t1, t2=t2, delta=dl, K=K,
                             n_rho=n_rho, n_phi=n_phi, sincos=sc, m_star=m,
                             status=st, secs=time.time() - t0))
            print("%-9s K=%d grid=%dx%d sin=%d  m*=%.6f  (%s, %.1fs)"
                  % (name, K, n_rho, n_phi, sc, (m if m else -1),
                     "pass" if (m is not None and m < 0.1) else "FAIL/na",
                     time.time() - t0), flush=True)
    json.dump(rows, open(OUT / "dual_refine.json", "w"), indent=1)


if __name__ == "__main__":
    main()
