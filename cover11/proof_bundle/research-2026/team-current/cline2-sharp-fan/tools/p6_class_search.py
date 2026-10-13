# -*- coding: utf-8 -*-
"""P6 (v2): direct numeric minimisation of the covering radius over q0 fan class.

Variables x = (rho_0..rho_8, phi_1..phi_8, h1x,h1y,h2x,h2y)  [18 vars]
  rho_i  = |c_i| (ring modulus)   Phi = phi_1 (global rotation, fixed 0 for ring 0)
  the rings are taken in the order given by the sorted phi's (the ORDER is a free
  parameter, not assumed).
R is NOT a variable: R(x) = the covering radius of the 11 disks at the position
  minimising over hubs? No -- the hubs are variables, so
R(x) = max( boundary-defect , 2-centre radius of the hole witnesses ).
Objective: minimise R(x).
This is exactly the quantity to attack; the active set decides which q0 class we are in.
"""
import os, sys, math, json
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")

NPHI = 1440
TH = np.linspace(0, 2*np.pi, NPHI, endpoint=False)
BD = np.stack([np.cos(TH), np.sin(TH)], axis=1)

XS = np.linspace(-1, 1, 121)
GX, GY = np.meshgrid(XS, XS)
MASK = GX**2 + GY**2 <= 1.0
GRID = np.stack([GX[MASK], GY[MASK]], axis=1)
# IMPORTANT: include the origin and the core circle explicitly
EXTRA = np.array([[0.0, 0.0]] + [[math.cos(t), math.sin(t)] for t in np.linspace(0, 2*np.pi, 180, endpoint=False)])


def rings_of(x):
    rho = x[:9]
    ph = np.concatenate([[0.0], x[9:17]])
    return np.stack([rho*np.cos(ph), rho*np.sin(ph)], axis=1)


def hubs_of(x):
    return x[17:21].reshape(2, 2)


def Rval(x, return_parts=False):
    C = rings_of(x); H = hubs_of(x)
    db = np.linalg.norm(BD[:, None, :] - C[None, :, :], axis=2).min(axis=1).max()
    dg = np.linalg.norm(GRID[:, None, :] - C[None, :, :], axis=2).min(axis=1)
    de = np.linalg.norm(EXTRA[:, None, :] - C[None, :, :], axis=2).min(axis=1)
    hole = GRID[dg > db]
    if len(hole) == 0:
        rh = 0.0
    else:
        dh = np.linalg.norm(hole[:, None, :] - H[None, :, :], axis=2).min(axis=1)
        rh = float(dh.max())
    dhe = np.linalg.norm(EXTRA[:, None, :] - H[None, :, :], axis=2).min(axis=1)
    rh = max(rh, float(dhe.max()))
    if return_parts:
        return db, rh, C, H, hole
    return max(db, rh)


def obj(x):
    try:
        v = Rval(x)
        if not np.isfinite(v):
            return 1e6
        # keep rings inside the unit disk
        pen = 0.0
        for r in x[:9]:
            if r > 1.0:
                pen += (r-1.0)**2
        return v + 10*pen
    except Exception:
        return 1e6


def seed_from_object():
    import json as js
    p = os.path.join(OUT, "certified_object_copy.json")
    if not os.path.exists(p):
        p = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..",
                                         "n11", "upper", "certified_object.json"))
    with open(p, "r", encoding="utf-8-sig") as f:
        o = js.load(f)
    Cl = [(int(a)/1e17, int(b)/1e17) for a, b in o["centers_scaled_1e17"]]
    ring = [1, 3, 4, 5, 6, 7, 8, 9, 10]
    hub = [0, 2]
    rr = [math.hypot(*Cl[i]) for i in ring]
    ph = [math.atan2(Cl[i][1], Cl[i][0]) for i in ring]
    k = int(np.argmin(ph))
    ph = [p - ph[k] for p in ph]
    idx = np.argsort(ph)
    rr = [rr[i] for i in idx]
    ph = [ph[i] for i in idx]
    x = np.concatenate([rr, ph[1:], np.array(Cl[hub[0]] + Cl[hub[1]])])
    return x


if __name__ == "__main__":
    lines = []
    def P(s=""):
        lines.append(s); print(s)

    x0 = seed_from_object()
    P("seed R = %.12f" % obj(x0))
    best = (obj(x0), x0.copy())
    rng = np.random.default_rng(0)
    for trial in range(6):
        xs = x0.copy() if trial == 0 else x0 + np.concatenate([
            0.004*rng.standard_normal(9), 0.01*rng.standard_normal(8), 0.005*rng.standard_normal(4)])
        res = minimize(obj, xs, method='Nelder-Mead',
                       options=dict(maxiter=60000, maxfev=60000, xatol=1e-12,
                                    fatol=1e-14, adaptive=True))
        v = obj(res.x)
        P("trial %d: start=%.12f -> %.12f" % (trial, obj(xs), v))
        if v < best[0]:
            best = (v, res.x.copy())
    db, rh, C, H, hole, = Rval(best[1], return_parts=True)
    P("")
    P("BEST R = %.12f   (boundary defect %.12f, hole 2-centre %.12f)" % (best[0], db, rh))
    P("ring moduli : %s" % np.round(best[1][:9], 10).tolist())
    P("ring angles : %s" % np.round(np.concatenate([[0.0], best[1][9:17]]), 10).tolist())
    P("hubs        : %s" % np.round(best[1][17:21], 10).tolist())
    P("ring-mean   : %.10f" % best[1][:9].mean())
    with open(os.path.join(OUT, "p6_class_search.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
