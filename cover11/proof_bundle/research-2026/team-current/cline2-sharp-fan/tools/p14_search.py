# -*- coding: utf-8 -*-
"""P14 (clean): covering-radius landscape, seed verified by construction."""
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

NR, NTH = 600, 2880
rs = np.linspace(0, 1, NR)
ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)


def unpack(x):
    rho = np.abs(x[:9])
    ph = np.concatenate([[0.0], x[9:17]])
    C = np.stack([rho*np.cos(ph), rho*np.sin(ph)], axis=1)
    H = x[17:21].reshape(2, 2)
    return C, H


def seed():
    C = np.zeros((9, 2)); H = np.zeros((2, 2))
    rho = np.linalg.norm(C0[RING], axis=1)
    psi = np.arctan2(C0[RING, 1], C0[RING, 0])
    order = np.argsort(psi)
    rho = rho[order]; psi = psi[order]
    psi = np.mod(psi - psi[0], 2*np.pi)         # rotate so ring 0 has angle 0 (mod 2pi)
    # put the angle-0 ring FIRST (it is already first after the shift)
    assert abs(psi[0]) < 1e-12, psi
    x = np.concatenate([rho, psi[1:], C0[HUB[0]], C0[HUB[1]]])
    return x


def coverval(x, refine=True, pts=PTS):
    C, H = unpack(x)
    ALL = np.vstack([C, H])
    d = np.linalg.norm(pts[:, None, :]-ALL[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d)); best = float(d[i])
    if refine:
        def neg(p):
            if p[0]**2+p[1]**2 > 1.0:
                return 1e4*(p[0]**2+p[1]**2-1.0)
            return -np.min(np.linalg.norm(ALL-p, axis=1))
        res = minimize(neg, pts[i], method='Nelder-Mead',
                       options=dict(xatol=1e-14, fatol=1e-16, maxiter=4000))
        best = max(best, -res.fun)
    return best


if __name__ == "__main__":
    lines = []
    def P(s=""):
        lines.append(s); print(s)
    x0 = seed()
    C, H = unpack(x0)
    ALL = np.vstack([C, H])
    # verification: the reconstructed full set equals the original set
    A = np.sort(ALL.view([('x', float), ('y', float)]), axis=0)
    B = np.sort(C0.view([('x', float), ('y', float)]), axis=0)
    P("reconstruction check |sorted diff|inf = %.3e" %
      np.abs(ALL[np.lexsort((ALL[:, 1], ALL[:, 0]))] -
             C0[np.lexsort((C0[:, 1], C0[:, 0]))]).max())
    # direct covering radius of the ORIGINAL set (ground truth)
    d0 = np.linalg.norm(PTS[:, None, :]-C0[None, :, :], axis=2).min(axis=1)
    def neg0(p):
        if p[0]**2+p[1]**2 > 1.0:
            return 1e4*(p[0]**2+p[1]**2-1.0)
        return -np.min(np.linalg.norm(C0-p, axis=1))
    r0 = minimize(neg0, PTS[int(np.argmax(d0))], method='Nelder-Mead',
                  options=dict(xatol=1e-14, fatol=1e-16, maxiter=4000))
    P("ORIGINAL covering radius (grid+refine) = %.17f   (R=%.17f, diff %+.3e)"
      % (-r0.fun, R0, -r0.fun-R0))
    P("coverval(seed) = %.17f" % coverval(x0))
    P("")
    P("=== MULTI-START LOCAL MINIMISATION ===")
    best = (coverval(x0), x0.copy())
    rng = np.random.default_rng(5)
    for sc, ntr in [(0.0, 1), (0.001, 2), (0.004, 3), (0.01, 3), (0.03, 2)]:
        for t in range(ntr):
            xs = x0.copy() if sc == 0 else x0 + np.concatenate([
                sc*rng.standard_normal(9), sc*rng.standard_normal(8),
                2*sc*rng.standard_normal(4)])
            res = minimize(coverval, xs, method='Nelder-Mead',
                           options=dict(maxiter=30000, maxfev=30000, xatol=1e-12,
                                        fatol=1e-15, adaptive=True))
            v = coverval(res.x)
            P("  sc=%.3f t=%d: %.12f -> %.12f  (delta %+.3e)" % (sc, t, coverval(xs), v, v-best[0]))
            if v < best[0]:
                best = (v, res.x.copy()); P("      *** new best")
    P("")
    P("BEST = %.17f  (candidate %+.3e)" % (best[0], best[0]-R0))
    Cb, Hb = unpack(best[1])
    P("moduli: %s" % np.round(np.linalg.norm(Cb, axis=1), 10).tolist())
    P("angles: %s" % np.round(np.arctan2(Cb[:, 1], Cb[:, 0]), 10).tolist())
    P("hubs  : %s" % np.round(Hb, 10).tolist())
    with open(os.path.join(OUT, "p14_search.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
