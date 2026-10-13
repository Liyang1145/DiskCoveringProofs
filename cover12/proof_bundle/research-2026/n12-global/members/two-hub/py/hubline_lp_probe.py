"""hubline_lp_probe.py -- PROPOSALS ONLY (numeric, no certification).

Lead's h-line chart: h1 = (x-s, y), h2 = (x+s, y), s=d/2, x,y >= 0 (rotation /
reflection / relabelling).  From the core point (0,-a), a = 1-2U:
   (x-s)^2 + (y+a)^2 <= U^2   =>   y <= e0 = 3U-1,
and the core point with -x gives x <= s + e0.  Domain:
   s in (0,U), x in [0, s+e0], y in [0, e0], (x+s)^2 + y^2 <= (1-U)^2.
Exposed hub arcs sit at centres 0 and pi with halfwidth pi - acos(s/U) (no hub
direction unwrap, no near-zero angle singularity).

For each sampled (s,x,y) we solve the same LP as dual2/dual_refine but with this
chart geometry, and additionally test whether ONE weight triple (per s) can
cover a whole set of (x,y) samples at the fixed ratio t = 0.1.
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
import dual_refine as D  # basis_arc / basis_arc_int (float, numeric only)

OUT = HERE.parent / "evidence"
U = D.U
A_CORE = 1 - 2 * U
E0 = 3 * U - 1
K = 4
PER = 1 + 2 * K


def alpha_of_rho(rho):
    return math.acos(max(-1.0, min(1.0, (1 + rho * rho - U * U) / (2 * rho))))


def build(s, x, y, n_rho=24, n_phi=96):
    h1 = np.array([x - s, y])
    h2 = np.array([x + s, y])
    b = math.acos(max(-1.0, min(1.0, s / U)))
    hw = math.pi - b
    E = [(math.pi, hw), (0.0, hw)]
    nw = 3 * PER
    req = np.zeros(nw)
    req[0:PER] = D.basis_arc(0.0, math.pi, K, True)
    for j in (0, 1):
        req[(j + 1) * PER:(j + 2) * PER] += D.basis_arc(E[j][0], E[j][1], K, True)
    rows = []
    for rho in np.linspace(1 - U, math.sqrt(1 - U * U), n_rho):
        ah = alpha_of_rho(float(rho))
        for phi in np.linspace(0, 2 * math.pi, n_phi, endpoint=False):
            c = float(rho) * np.array([math.cos(phi), math.sin(phi)])
            row = np.zeros(nw)
            row[0:PER] += D.basis_arc(phi, ah, K, True)
            for j, hj in enumerate((h1, h2)):
                ell = float(np.hypot(*(c - hj)))
                if ell < 2 * U:
                    bet = math.acos(max(-1.0, min(1.0, ell / (2 * U))))
                    psi = math.atan2(*(c - hj)[::-1])
                    row[(j + 1) * PER:(j + 2) * PER] += \
                        D.basis_arc_int(psi, bet, E[j][0], E[j][1], K, True)
            rows.append(row)
    return np.array(rows), req


def solve_single(s, x, y, n_rho=24, n_phi=96):
    A, req = build(s, x, y, n_rho, n_phi)
    return _lp(A, req)


def _lp(blocks, reqs):
    """minimise m s.t. cap(block, ring) <= m * req(block)  (reqs may be a list)."""
    if not isinstance(reqs, list):
        blocks, reqs = [blocks], [reqs]
    nw = 3 * PER
    nvar = nw + 6 * K + 1
    mi = nw + 6 * K
    A_ubs, b_ubs = [], []
    for A, req in zip(blocks, reqs):
        M = np.zeros((A.shape[0], nvar))
        M[:, 0:nw] = A - req[None, :]        # cap - m*req <= 0 is bilinear; instead
        A_ubs.append(M)                       # we fix m = 0.1 via the ratio form below
        b_ubs.append(np.zeros(A.shape[0]))
    # ratio form: cap <= t*req  with t fixed (feasibility) -- here we minimise the
    # *normalised* max: introduce z = m, constraints cap - m*req_scale <= 0 with
    # req_scale = req / req_average is nonlinear; hence we use the standard trick:
    # variables w plus m, and constraints cap(row) - m * req_hat <= 0 is bilinear in
    # (w,m).  Instead we minimise the ratio by bisection on t (feasibility LPs).
    return None


def feasible_at_t(blocks, reqs, t):
    nw = 3 * PER
    nvar = nw + 6 * K
    A_ubs, b_ubs = [], []
    for A, req in zip(blocks, reqs):
        M = np.zeros((A.shape[0], nvar))
        M[:, 0:nw] = A - t * req[None, :]
        A_ubs.append(M)
        b_ubs.append(np.zeros(A.shape[0]))
    ncoef = 2 * K
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
    A_ub = np.vstack([np.vstack(A_ubs), np.array(rows2)])
    b_ub = np.concatenate([np.concatenate(b_ubs), np.array(b2)])
    A_eq = np.zeros((1, nvar))
    A_eq[0, 0:nw] = reqs[0]
    b_eq = np.array([1.0])
    c = np.zeros(nvar)
    bounds = [(0.0, None)] + [(None, None)] * (PER - 1) + [(None, None)] * (2 * PER) + \
             [(0.0, None)] * (3 * ncoef)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds,
                  method="highs")
    return res.status == 0


def main():
    t0 = time.time()
    ss = [0.05, 0.1, 0.2, 0.35, 0.55]
    rows = []
    for s in ss:
        xmax = s + E0
        ymax = min(E0, math.sqrt(max(0.0, (1 - U) ** 2 - (xmax + s) ** 2)) if (xmax + s) < 1 - U else E0)
        pts = []
        for (xf, yf) in ((0.0, 0.0), (0.0, 0.5), (0.0, 1.0), (0.5, 0.0), (1.0, 0.0),
                         (0.5, 0.5), (1.0, 0.5), (0.25, 1.0)):
            x = xf * xmax
            y = yf * E0
            if (x + s) ** 2 + y * y <= (1 - U) ** 2 + 1e-12 and y <= E0 + 1e-12:
                pts.append((x, y))
        blocks, reqs = [], []
        for (x, y) in pts:
            A, req = build(s, x, y, n_rho=20, n_phi=72)
            blocks.append(A)
            reqs.append(req)
        # joint: one weight per s covering all (x,y) samples?
        lo, hi = 0.02, 0.12
        for _ in range(14):
            mid = (lo + hi) / 2
            if feasible_at_t(blocks, reqs, mid):
                hi = mid
            else:
                lo = mid
        rows.append(dict(s=s, n_pts=len(pts), xmax=xmax,
                         joint_t_min=hi, pts=pts))
        print("s=%.3f  pts=%d  joint t* = %.5f (feasible<1.0 means one weight per s "
              "covers all sampled (x,y))  %.0fs" % (s, len(pts), hi, time.time() - t0),
              flush=True)
    json.dump(rows, open(OUT / "hubline_lp_probe.json", "w"), indent=1)
    print("done %.0fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
