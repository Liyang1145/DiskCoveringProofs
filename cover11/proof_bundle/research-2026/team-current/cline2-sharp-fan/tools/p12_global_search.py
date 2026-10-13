# -*- coding: utf-8 -*-
"""P12: global numerical minimisation of the covering radius + class comparison.

Evaluator R(x) for x = (rho_0..rho_8, phi_1..phi_8 (phi_0=0), h1x,h1y,h2x,h2y):
   R(x) = max_P min( min_i |P-c_i| , min_j |P-h_j| )   over a dense point set in D
        = the covering radius of the 11 disks.
This is a LOWER bound on the true covering radius for a finite point set; with a fine
grid plus local refinement of the argmax it is accurate to ~1e-9 and is used only as a
search guide (numeric, not a certificate).
"""
import os, sys, math, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C0 = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R0 = 0.3799838531198387090485181795734298538115979028

N = 301
XS = np.linspace(-1, 1, N)
GX, GY = np.meshgrid(XS, XS)
MK = GX**2+GY**2 <= 1.0
PTS = np.stack([GX[MK], GY[MK]], axis=1)                    # ~ 70k points


def unpack(x):
    rho = x[:9]
    ph = np.concatenate([[0.0], x[9:17]])
    C = np.stack([rho*np.cos(ph), rho*np.sin(ph)], axis=1)
    H = x[17:21].reshape(2, 2)
    return C, H


def coverval(x, pts=PTS, refine=True):
    C, H = unpack(x)
    d = np.linalg.norm(pts[:, None, :]-C[None, :, :], axis=2).min(axis=1)
    dh = np.linalg.norm(pts[:, None, :]-H[None, :, :], axis=2).min(axis=1)
    v = np.minimum(d, dh)
    i = int(np.argmax(v)); best = float(v[i]); arg = pts[i]
    if refine:
        from scipy.optimize import minimize as _m
        def neg(p):
            if p[0]**2+p[1]**2 > 1.0:
                return 1e3*(p[0]**2+p[1]**2-1.0) + 0.0
            dd = np.min(np.linalg.norm(C-p, axis=1))
            hh = np.min(np.linalg.norm(H-p, axis=1))
            return -min(dd, hh)
        res = _m(neg, arg, method='Nelder-Mead',
                 options=dict(xatol=1e-13, fatol=1e-15, maxiter=3000))
        if -res.fun > best:
            best = -res.fun
    return best


def seed():
    """FIXED: phi_0 = 0 must be applied to the LOWEST-index ring kept, and all rings
    including the one entering slot 0 must be reordered consistently."""
    ring = [1, 3, 4, 5, 6, 7, 8, 9, 10]
    rh = np.linalg.norm(C0[ring], axis=1)
    ph = np.arctan2(C0[ring, 1], C0[ring, 0])
    idx = np.argsort(ph)
    rh = rh[idx]; ph = ph[idx]
    ph = ph - ph[0]                       # rotate so the first kept ring sits at angle 0
    ph = np.mod(ph, 2*np.pi)
    return np.concatenate([rh, ph[1:], C0[0], C0[2]])


if __name__ == "__main__":
    from scipy.optimize import minimize
    lines = []
    def P(s=""):
        lines.append(s); print(s)
    x0 = seed()
    v0 = coverval(x0)
    P("seed: R = %.17f  (claim %.17f, diff %+.3e)" % (v0, R0, v0-R0))
    best = (v0, x0.copy())
    rng = np.random.default_rng(3)
    P("")
    for scale, ntrial in [(0.0, 1), (0.002, 4), (0.006, 4), (0.02, 3)]:
        for t in range(ntrial):
            xs = x0.copy() if scale == 0 else x0 + np.concatenate([
                scale*rng.standard_normal(9), scale*rng.standard_normal(8),
                scale*2*rng.standard_normal(4)])
            res = minimize(coverval, xs, method='Nelder-Mead',
                           options=dict(maxiter=30000, maxfev=30000, xatol=1e-12,
                                        fatol=1e-14, adaptive=True))
            v = coverval(res.x)
            P("scale=%.3f trial %d: start %.12f -> %.12f" % (scale, t, coverval(xs), v))
            if v < best[0]:
                best = (v, res.x.copy())
    P("")
    P("BEST = %.17f" % best[0])
    C, H = unpack(best[1])
    P("rings: %s" % np.round(C, 12).tolist())
    P("hubs : %s" % np.round(H, 12).tolist())
    P("moduli: %s" % np.round(np.linalg.norm(C, axis=1), 12).tolist())
    P("moduli - (1-R): %s" % np.round(np.linalg.norm(C, axis=1)-(1-best[0]), 9).tolist())
    with open(os.path.join(OUT, "p12_global_search.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
