# -*- coding: utf-8 -*-
"""P13: corner function of the rings (upper radial envelope) + global search.

For a ring configuration c_0..c_8 (radius R), define for each direction theta
    f(theta) = min_i |P(theta) - c_i|,   P(theta) = (cos theta, sin theta)
The ring-hole is  {x in D : |x - c_i| > R  for all i}.  Then
    covering (rings + 2 hubs, radius R)  <=>  boundary covered  AND  for every theta
    with f(theta) > R  and  R < r < f(theta):  B(x) is in one of the hubs.
A good finite surrogate for the hub side: the "corner function"
    g(theta) = f(theta)  at the local maxima, plus the tips.
This script computes the exact covering radius of the 11 disks by fine grid + local
refinement, and runs a multi-start local minimisation over (rho_i, phi_i, hubs).
"""
import os, sys, math, json
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C0 = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R0 = 0.3799838531198387090485181795734298538115979028
RING = [1, 3, 4, 5, 6, 7, 8, 9, 10]
HUB = [0, 2]

# dense sampling: polar grid is much better than cartesian for this geometry
NR = 400
NTH = 1440
rs = np.linspace(0, 1, NR)
ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([RR.ravel()*np.cos(TT.ravel()), RR.ravel()*np.sin(TT.ravel())], axis=1)


def unpack(x):
    rho = x[:9]
    ph = np.concatenate([[0.0], x[9:17]])
    C = np.stack([rho*np.cos(ph), rho*np.sin(ph)], axis=1)
    H = x[17:21].reshape(2, 2)
    return C, H


def coverval(x, refine=True):
    C, H = unpack(x)
    d = np.linalg.norm(PTS[:, None, :]-np.vstack([C, H])[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d)); best = float(d[i]); arg = PTS[i]
    if refine:
        ALL = np.vstack([C, H])
        def neg(p):
            if p[0]**2+p[1]**2 > 1.0:
                return 1e3*(p[0]**2+p[1]**2-1.0)
            return -np.min(np.linalg.norm(ALL-p, axis=1))
        res = minimize(neg, arg, method='Nelder-Mead',
                       options=dict(xatol=1e-14, fatol=1e-16, maxiter=4000))
        if -res.fun > best:
            best = -res.fun
    return best


def seed():
    rh = np.linalg.norm(C0[RING], axis=1)
    ph = np.arctan2(C0[RING, 1], C0[RING, 0])
    idx = np.argsort(ph)
    rh = rh[idx]; ph = np.mod(ph[idx]-ph[idx][0], 2*np.pi)
    return np.concatenate([rh, ph[1:], C0[HUB[0]], C0[HUB[1]]])


if __name__ == "__main__":
    lines = []
    def P(s=""):
        lines.append(s); print(s)
    x0 = seed()
    v0 = coverval(x0)
    P("seed covering radius = %.17f (R=%.17f, diff %+.3e)" % (v0, R0, v0-R0))
    C, H = unpack(x0)
    ALL = np.vstack([C, H])
    d = np.linalg.norm(PTS[:, None, :]-ALL[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d))
    P("worst sampled point = %s   dist = %.17f   nearest centres: %s"
      % (np.round(PTS[i], 8).tolist(), d[i],
         np.argsort(np.linalg.norm(ALL-PTS[i], axis=1))[:3].tolist()))
    P("")
    P("=== MULTI-START LOCAL MINIMISATION of the covering radius ===")
    best = (v0, x0.copy())
    rng = np.random.default_rng(11)
    for sc, ntr in [(0.0, 1), (0.0015, 3), (0.005, 3), (0.015, 2), (0.05, 1)]:
        for t in range(ntr):
            xs = x0.copy() if sc == 0 else x0 + np.concatenate([
                sc*rng.standard_normal(9), sc*rng.standard_normal(8),
                2*sc*rng.standard_normal(4)])
            res = minimize(coverval, xs, method='Nelder-Mead',
                           options=dict(maxiter=40000, maxfev=40000, xatol=1e-12,
                                        fatol=1e-15, adaptive=True))
            v = coverval(res.x)
            P("  scale %.3f trial %d: %.12f -> %.12f  (improvement %+.3e)"
              % (sc, t, coverval(xs), v, v-v0))
            if v < best[0]:
                best = (v, res.x.copy())
                P("      *** new best")
    P("")
    P("BEST covering radius = %.17f   (candidate %+.3e)" % (best[0], best[0]-v0))
    Cb, Hb = unpack(best[1])
    P("best rings moduli: %s" % np.round(np.linalg.norm(Cb, axis=1), 10).tolist())
    P("best rings angles: %s" % np.round(np.arctan2(Cb[:, 1], Cb[:, 0]), 10).tolist())
    P("best hubs        : %s" % np.round(Hb, 10).tolist())
    with open(os.path.join(OUT, "p13_search.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
