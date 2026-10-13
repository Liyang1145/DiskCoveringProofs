"""dual2.py -- corrected k=10 dual kernel (fixes the arc-intersection wrapping bug
reported by Lead) plus independent cross-checks.

Objects (all at the fixed radius U; see REDUCTION.md):
  hub-1 direction = 0, hub-2 at angle delta, norms t1,t2, h_j = t_j u(delta_j)
  d = |h1-h2|, b = acos(clamp(d/(2U),-1,1)), E_j = arc on S(h_j,U) outside
  B(h_{j'},U): centre = away_j = dir(h_j - h_{j'}), halfwidth pi - b
  (full circle when d >= 2U; for d = 0 the hubs must be MERGED - handled by
  the caller, not by inventing two semicircles of separate weights).
  D-clip: since |h_j| + U may exceed 1, only E_j cap D is actually required.
  ring: rho in [1-U, sqrt(1-U^2)] (inner-root form, coverage-preserving),
  phi; A0 = arc(phi, alpha(rho)) on S^1;
  A_j = arc(psi_j, beta_j) on S(h_j,U), psi_j = dir(c - h_j),
  beta_j = acos(|c-h_j|/(2U)) if |c-h_j| < 2U else empty.

COUPLED CONTRIBUTION (definition used in the dual):
  cap(rho,phi) = int_{A0} W0 + int_{E1 cap A1} W1 + int_{E2 cap A2} W2
  req          = int_{S^1} W0 + int_{E1 cap D} W1 + int_{E2 cap D} W2
  criterion    : 10 * max_{rho,phi} cap  <  req        (then ten rings cannot
  cover S^1 and E1 cap D and E2 cap D simultaneously).
  Any point of (partial H) cap int D is covered by a ring (perturbation +
  closedness), so the requirement is valid; cap is an upper bound of a ring's
  contribution because A_j cap E_j sup A_j cap E_j cap D.

FIXED KERNEL: arc-intersection integrals sum over shifts -2pi, 0, +2pi of the
unrolled A interval against B's interval (two pieces are possible when
hA + hB > pi; the old single-piece version underestimated cap).
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

U = 0.361102963744508672616920293904
TWO_PI = 2 * math.pi
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "evidence"


def wrap(x):
    return (x + math.pi) % TWO_PI - math.pi


# ------------------------------------------------------------------ basis
def basis_arc(center, half, sincos=True, K=4):
    n = 1 + K * (2 if sincos else 1)
    b = np.zeros(n)
    b[0] = 2.0 * half
    for k in range(1, K + 1):
        b[k] = (math.sin(k * (center + half)) - math.sin(k * (center - half))) / k
        if sincos:
            b[K + k] = -(math.cos(k * (center + half)) - math.cos(k * (center - half))) / k
    return b


def basis_shifted(lo, hi, cB, sincos=True, K=4):
    if hi <= lo:
        return np.zeros(1 + K * (2 if sincos else 1))
    return basis_arc(cB + 0.5 * (lo + hi), 0.5 * (hi - lo), sincos, K)


def basis_arc_int(cA, hA, cB, hB, sincos=True, K=4):
    """FIXED: sum over the three shifts, so wrapped second pieces are included."""
    d = wrap(cA - cB)
    out = None
    for sh in (-TWO_PI, 0.0, TWO_PI):
        lo = max(-hB, d - hA + sh)
        hi = min(hB, d + hA + sh)
        if hi <= lo:
            continue
        v = basis_shifted(lo, hi, cB, sincos, K)
        out = v if out is None else out + v
    if out is None:
        return np.zeros(1 + K * (2 if sincos else 1))
    return out


def weight_eval(coeffs, theta, sincos=True, K=4):
    v = coeffs[0]
    for k in range(1, K + 1):
        v += coeffs[k] * math.cos(k * theta)
        if sincos:
            v += coeffs[K + k] * math.sin(k * theta)
    return v


def quad_int_arc(coeffs, center, half, sincos=True, K=4, n=4001):
    """INDEPENDENT numerical integration of w over an arc (calibration)."""
    th = np.linspace(center - half, center + half, n)
    w = np.full_like(th, coeffs[0])
    for k in range(1, K + 1):
        w += coeffs[k] * np.cos(k * th)
        if sincos:
            w += coeffs[K + k] * np.sin(k * th)
    return float(np.trapezoid(w, th))


def quad_int_arc_int(coeffs, cA, hA, cB, hB, sincos=True, K=4, n=200001):
    """INDEPENDENT quadrature over A cap B (circle-correct, two pieces)."""
    th = np.linspace(-math.pi, math.pi, n, endpoint=False)
    a = np.abs(wrap(th - cA)) <= hA
    b = np.abs(wrap(th - cB)) <= hB
    w = np.full_like(th, coeffs[0])
    for k in range(1, K + 1):
        w += coeffs[k] * np.cos(k * th)
        if sincos:
            w += coeffs[K + k] * np.sin(k * th)
    return float(np.sum(w[a & b]) * (TWO_PI / n))


# ------------------------------------------------------------------ geometry
def hub_geom(t1, t2, delta):
    h1 = np.array([t1, 0.0])
    h2 = t2 * np.array([math.cos(delta), math.sin(delta)])
    d = float(np.hypot(*(h1 - h2)))
    if d > 1e-12:
        b = math.acos(max(-1.0, min(1.0, d / (2 * U))))
        away1 = math.atan2(*(h1 - h2)[::-1])
        away2 = math.atan2(*(h2 - h1)[::-1])
    else:
        b = math.pi / 2
        away1, away2 = 0.0, math.pi
    return h1, h2, d, b, away1, away2


def d_clip_arc(t, K=4, sincos=True):
    """Arc of S(h_j,U) inside D (centre = inward dir, halfwidth pi - t0) or None."""
    if t + U <= 1.0:
        return None
    z = (1.0 - t * t - U * U) / (2.0 * t * U)
    th0 = math.acos(max(-1.0, min(1.0, z)))
    return (math.pi - th0)  # halfwidth about the inward direction


def build(t1, t2, delta, K=4, sincos=True, n_rho=40, n_phi=144, clip_req=True):
    h1, h2, d, b, away1, away2 = hub_geom(t1, t2, delta)
    E = [(away1, math.pi - b), (away2, math.pi - b)]
    per = 1 + K * (2 if sincos else 1)
    nw = 3 * per
    req = np.zeros(nw)
    req[0:per] = basis_arc(0.0, math.pi, sincos, K)
    for j, (hj, (cw, hw)) in enumerate(zip((h1, h2), E)):
        blk = basis_arc(cw, hw, sincos, K)
        if clip_req:
            t = float(np.hypot(*hj))
            h_in = d_clip_arc(t, K, sincos)
            if h_in is not None:
                base = math.atan2(hj[1], hj[0])
                blk = basis_arc_int(cw, hw, base + math.pi, h_in, sincos, K)
        req[(j + 1) * per:(j + 2) * per] += blk
    rows = []
    for rho in np.linspace(1.0 - U, math.sqrt(1.0 - U * U), n_rho):
        ah = math.acos(max(-1, min(1, (1 + rho * rho - U * U) / (2 * rho))))
        for phi in np.linspace(0, TWO_PI, n_phi, endpoint=False):
            c = rho * np.array([math.cos(phi), math.sin(phi)])
            row = np.zeros(nw)
            row[0:per] += basis_arc(phi, ah, sincos, K)
            for j, hj in enumerate((h1, h2)):
                ell = float(np.hypot(*(c - hj)))
                if ell < 2 * U:
                    bet = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
                    psi = math.atan2(*(c - hj)[::-1])
                    row[(j + 1) * per:(j + 2) * per] += \
                        basis_arc_int(psi, bet, E[j][0], E[j][1], sincos, K)
            rows.append(row)
    return np.array(rows), req, dict(h1=h1, h2=h2, d=d, b=b, E=E, per=per)


def solve(t1, t2, delta, K=4, sincos=True, n_rho=40, n_phi=144, clip_req=True):
    A, req, geo = build(t1, t2, delta, K, sincos, n_rho, n_phi, clip_req)
    nr, nw = A.shape
    per = nw // 3
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
        rows2.append(r); b2.append(0.0)
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
    if res.status != 0:
        return dict(ok=False, msg=res.message, **{k: v for k, v in geo.items()
                                                  if k in ("d", "b")})
    w = res.x[0:nw]
    return dict(ok=True, m_star=float(res.fun), weights=[w[i * per:(i + 1) * per]
                                                         for i in range(3)],
                req=req, A=A, geo=geo, per=per, m_basis=res.x[0:nw])


# ------------------------------------------------------- verification tools
def cap_at(cfg, wflat, rho, phi, K=4, sincos=True):
    """coupled contribution at one ring position; wflat = flat weight vector."""
    per = cfg["per"]
    h1, h2, E = cfg["geo"]["h1"], cfg["geo"]["h2"], cfg["geo"]["E"]
    c = rho * np.array([math.cos(phi), math.sin(phi)])
    ah = math.acos(max(-1, min(1, (1 + rho * rho - U * U) / (2 * rho))))
    v = 0.0
    blk = basis_arc(phi, ah, sincos, K)
    v += float(blk @ wflat[0:per])
    for j, hj in enumerate((h1, h2)):
        ell = float(np.hypot(*(c - hj)))
        if ell < 2 * U:
            bet = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
            psi = math.atan2(*(c - hj)[::-1])
            BLK = basis_arc_int(psi, bet, E[j][0], E[j][1], sincos, K)
            v += float(BLK @ wflat[(j + 1) * per:(j + 2) * per])
    return v


def refine_max(cfg, w, K=4, sincos=True, n_start=12, seed=1):
    """local maximisation of cap over (rho,phi) from grid starts."""
    A = cfg["A"]
    vals = A @ cfg["m_basis"]
    order = np.argsort(vals)[::-1][:n_start]
    n_rho, n_phi = 40, 144
    rhos = np.linspace(1.0 - U, math.sqrt(1.0 - U * U), n_rho)
    phis = np.linspace(0, TWO_PI, n_phi, endpoint=False)
    best = (-1.0, None)
    for idx in order:
        i, j = divmod(int(idx), n_phi)
        x0 = np.array([rhos[i], phis[j]])
        res = minimize(lambda x: -cap_at(cfg, w, x[0], x[1], K, sincos),
                       x0, method="Nelder-Mead",
                       options=dict(xatol=1e-12, fatol=1e-14, maxfev=4000,
                                    adaptive=True))
        if -res.fun > best[0]:
            best = (-res.fun, res.x.copy())
    return best
