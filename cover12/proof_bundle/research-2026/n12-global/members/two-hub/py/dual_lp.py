"""dual_lp.py -- LP feasibility test for the k=10 joint capacity dual.

Dual form tested (per hub configuration H=(t1,t2,delta), hub-1 direction = 0):

  required = int_{S^1} W0 + int_{E_1} W1 + int_{E_2} W2          (normalised to 1)
  capture(rho,phi) = int_{A0(rho,phi)} W0
                   + int_{E_1 cap A1(rho,phi)} W1
                   + int_{E_2 cap A2(rho,phi)} W2
  need:  max over the ring domain of capture  <  required/10 = 0.1

where
  rings: rho in [1-U, sqrt(1-U^2)], alpha(rho) = actual boundary halfwidth,
         phi arbitrary; A0 = arc(phi, alpha(rho));
  hubs : h_j = t_j u(delta_j); E_j = arc away from the other hub, halfwidth
         pi - acos(clamp(d/(2U))) (full circle when d>=2U);
  A_j  = arc(psi_j, beta_j), psi_j = dir(c-h_j), beta_j = acos(|c-h_j|/(2U))
         if |c-h_j| < 2U else empty.
Weights: W_j(theta) = a_j0 + sum_{k=1..K} a_jk cos(k theta), constrained by
a_j0 >= sum_k |a_jk| (sufficient for pointwise nonnegativity).

LHS is linear in the weight coefficients, so feasibility is an LP.  Float only:
this is a design/diagnostic instrument, not a certificate.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

U = 0.361102963744508672616920293904
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "evidence"


def wrap(x):
    return (x + math.pi) % (2 * math.pi) - math.pi


def arc_int_basis(center, half, K):
    """Return basis vector b with  int_A w = b . coeffs  for arc (center,half)."""
    b = np.zeros(K + 1)
    b[0] = 2.0 * half
    for k in range(1, K + 1):
        b[k] = (math.sin(k * (center + half)) - math.sin(k * (center - half))) / k
    return b


def arc_intersect_int_basis(cA, hA, cB, hB, K):
    """int over A cap B of w, basis vector (A = (cA,hA), B = (cB,hB))."""
    d = wrap(cA - cB)
    lo = max(-hB, d - hA)
    hi = min(hB, d + hA)
    if hi <= lo:
        return np.zeros(K + 1)
    c, h = cB + 0.5 * (lo + hi), 0.5 * (hi - lo)
    return arc_int_basis(c, h, K)


def alpha_of_rho(rho):
    return math.acos(max(-1.0, min(1.0, (1.0 + rho * rho - U * U) / (2.0 * rho))))


def hub_geom(t1, t2, delta):
    h1 = np.array([t1, 0.0])
    h2 = t2 * np.array([math.cos(delta), math.sin(delta)])
    d = float(np.hypot(*(h1 - h2)))
    if d > 0:
        b = math.acos(max(-1.0, min(1.0, d / (2 * U))))
    else:
        b = math.pi / 2
    away1 = math.atan2(*(h1 - h2)[::-1]) if d > 0 else 0.0
    away2 = math.atan2(*(h2 - h1)[::-1]) if d > 0 else math.pi
    return h1, h2, d, b, away1, away2


def build(t1, t2, delta, K=4, n_rho=26, n_phi=96):
    h1, h2, d, b, away1, away2 = hub_geom(t1, t2, delta)
    E = [(away1, math.pi - b), (away2, math.pi - b)]
    # ---- requirement coefficients (length 3*(K+1))
    nw = 3 * (K + 1)
    req = np.zeros(nw)
    req[0:K + 1] = arc_int_basis(0.0, math.pi, K)
    for j in (0, 1):
        c, h = E[j]
        req[(j + 1) * (K + 1):(j + 2) * (K + 1)] += arc_int_basis(wrap(c), h, K)
    # ---- ring constraints
    rows = []
    rhos = np.linspace(1.0 - U, math.sqrt(1.0 - U * U), n_rho)
    phis = np.linspace(0.0, 2 * math.pi, n_phi, endpoint=False)
    for rho in rhos:
        a_half = alpha_of_rho(float(rho))
        for phi in phis:
            c = float(rho) * np.array([math.cos(phi), math.sin(phi)])
            row = np.zeros(nw)
            row[0:K + 1] += arc_int_basis(phi, a_half, K)
            for j, hj in enumerate((h1, h2)):
                ell = float(np.hypot(*(c - hj)))
                if ell < 2 * U:
                    beta = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
                    psi = math.atan2(*(c - hj)[::-1])
                    row[(j + 1) * (K + 1):(j + 2) * (K + 1)] += \
                        arc_intersect_int_basis(psi, beta, E[j][0], E[j][1], K)
            rows.append(row)
    return np.array(rows), req, dict(t1=t1, t2=t2, delta=delta, d=d, b=b,
                                     n_ring=len(rows))


def solve(t1, t2, delta, K=4, n_rho=26, n_phi=96, verbose=False):
    A, req, info = build(t1, t2, delta, K, n_rho, n_phi)
    nr = A.shape[0]
    nw = 3 * (K + 1)
    naux = 3 * K
    nvar = nw + naux + 1
    mi = nw + naux                     # index of m
    # capture - m <= 0
    A_ub = np.zeros((nr, nvar))
    A_ub[:, 0:nw] = A
    A_ub[:, mi] = -1.0
    b_ub = np.zeros(nr)
    # nonneg  a_j0 - sum_k s_jk >= 0  ->  -a_j0 + sum s <= 0 ; |a_jk| <= s_jk
    rows2, b2 = [], []
    for j in range(3):
        r = np.zeros(nvar)
        r[j * (K + 1)] = -1.0
        for k in range(1, K + 1):
            r[nw + j * K + (k - 1)] = 1.0
        rows2.append(r)
        b2.append(0.0)
        for k in range(1, K + 1):
            r1 = np.zeros(nvar)
            r1[j * (K + 1) + k] = 1.0
            r1[nw + j * K + (k - 1)] = -1.0
            rows2.append(r1)
            b2.append(0.0)
            r2 = np.zeros(nvar)
            r2[j * (K + 1) + k] = -1.0
            r2[nw + j * K + (k - 1)] = -1.0
            rows2.append(r2)
            b2.append(0.0)
    A_ub = np.vstack([A_ub, np.array(rows2)])
    b_ub = np.concatenate([b_ub, np.array(b2)])
    A_eq = np.zeros((1, nvar))
    A_eq[0, 0:nw] = req
    b_eq = np.array([1.0])
    c = np.zeros(nvar)
    c[mi] = 1.0
    bounds = [(0.0, None)] + [(None, None)] * K + \
             [(None, None)] * (2 * (K + 1)) + [(0.0, None)] * naux + [(0.0, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds,
                  method="highs")
    out = dict(**info, K=K, status=("ok" if res.status == 0 else res.message),
               m_star=float(res.fun) if res.status == 0 else None,
               pass_criterion=(res.status == 0 and res.fun < 0.1))
    if verbose and res.status == 0:
        w = res.x[0:nw]
        out["weights"] = [w[j * (K + 1):(j + 1) * (K + 1)].tolist() for j in range(3)]
        # which ring constraints are active
        vals = A @ w
        out["max_ring_index"] = int(np.argmax(vals))
        out["ring_binding_value"] = float(vals.max())
    return out


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    cfgs = [
        ("extremal", 0.1197, 0.2625, 3.0715),
        ("near_merged", 0.02, 0.02, 1.5708),
        ("central_pair", 0.1197, 0.2307, math.pi),
        ("far_hub", 0.0833, 0.6389, math.pi),
        ("far_hub2", 0.05, 0.5, 2.2),
        ("mid", 0.15, 0.35, 2.6),
        ("maxnorm_equal", 0.2307, 0.2307, math.pi),
        ("far_max", 0.08334, 0.638897, 3.14159),
    ]
    rows = []
    for name, t1, t2, dl in cfgs:
        r = solve(t1, t2, dl, K=K)
        r["name"] = name
        rows.append(r)
        print("%-14s t1=%.4f t2=%.4f dlt=%.4f  m*=%.5f  %s"
              % (name, t1, t2, dl, (r["m_star"] if r["m_star"] is not None else -1),
                 "PASS" if r["pass_criterion"] else "fail"), flush=True)
    json.dump(rows, open(OUT / ("dual_lp_K%d.json" % K), "w"), indent=1)


if __name__ == "__main__":
    main()
