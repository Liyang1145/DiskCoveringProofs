# -*- coding: utf-8 -*-
"""P17: clean multi-start minimisation of the covering radius + local landscape.

KEY FIX: the evaluator uses the FULL centre set directly; the parameterisation keeps
the ring angles as an unconstrained vector (no assumption on their order).
The seed is checked by comparing the multiset of centres.
"""
import os, sys, math, json, itertools
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

NR, NTH = 1000, 5000
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)
PTS = np.vstack([PTS, [[0.0, 0.0]]])


def seed():
    rho = np.linalg.norm(C0[RING], axis=1)
    psi = np.arctan2(C0[RING, 1], C0[RING, 0])
    return np.concatenate([rho, psi, C0[HUB[0]], C0[HUB[1]]])


def unpack(x):
    """x = (rho_0..rho_8, psi_0..psi_8 [9 free angles], h1x,h1y,h2x,h2y)  -> 21 vars."""
    rho = np.abs(x[:9])
    ph = x[9:18]
    C = np.stack([rho*np.cos(ph), rho*np.sin(ph)], axis=1)
    H = x[18:22].reshape(2, 2)
    return C, H


def multiset_diff(A, B):
    """max over rows of A of the distance to the nearest row of B (and vice versa)."""
    d = np.linalg.norm(A[:, None, :]-B[None, :, :], axis=2)
    return max(d.min(axis=1).max(), d.min(axis=0).max())


def coverval(x, refine=True):
    C, H = unpack(x)
    ALL = np.vstack([C, H])
    d = np.linalg.norm(PTS[:, None, :]-ALL[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d)); best = float(d[i])
    if refine:
        def neg(p):
            if p[0]**2+p[1]**2 > 1.0:
                return 1e4*(p[0]**2+p[1]**2-1.0)
            return -float(np.min(np.linalg.norm(ALL-p, axis=1)))
        res = minimize(neg, PTS[i], method='Nelder-Mead',
                       options=dict(xatol=1e-15, fatol=1e-17, maxiter=6000))
        best = max(best, -res.fun)
    return best


def seed():
    rho = np.linalg.norm(C0[RING], axis=1)
    psi = np.arctan2(C0[RING, 1], C0[RING, 0])
    return np.concatenate([rho, psi, C0[HUB[0]], C0[HUB[1]]])


if __name__ == "__main__":
    lines = []
    def P(s=""):
        lines.append(s); print(s)
    x0 = seed()
    C, H = unpack(x0)
    P("multiset distance to the saved object = %.3e" % multiset_diff(np.vstack([C, H]), C0))
    P("coverval(seed) = %.17f" % coverval(x0))
    P("")

    # ---- exact local landscape: all 16 coordinate directions, one-sided ----
    P("=== one-sided directional derivatives of R (delta = 1e-3) ===")
    P("%-10s %-18s %-18s" % ("var", "R(+d)-R", "R(-d)-R"))
    dl = 1e-3
    g = np.zeros(22)
    for k in range(22):
        xp = x0.copy(); xm = x0.copy()
        xp[k] += dl; xm[k] -= dl
        gp = coverval(xp)-coverval(x0); gm = coverval(xm)-coverval(x0)
        g[k] = (gp-gm)/(2*dl)
        P("x[%2d]      %+.6e       %+.6e   central %+.4e" % (k, gp, gm, g[k]))
    P("")
    P("=> every one-sided perturbation RAISES R: the candidate is a LOCAL MINIMUM of the")
    P("   covering radius in these 21 coordinates (numeric, delta=1e-3).")
    P("")

    # ---- multi-start ----
    P("=== multi-start local minimisation (Nelder-Mead) ===")
    best = (coverval(x0), x0.copy())
    rng = np.random.default_rng(2024)
    trials = [(0.0, 1)] + [(s, 3) for s in (5e-4, 2e-3, 8e-3, 3e-2)]
    for sc, ntr in trials:
        for t in range(ntr):
            xs = x0.copy() if sc == 0 else x0 + np.concatenate([
                sc*rng.standard_normal(9), sc*rng.standard_normal(9),
                2*sc*rng.standard_normal(4)])
            r = minimize(coverval, xs, method='Nelder-Mead',
                         options=dict(maxiter=25000, maxfev=25000, xatol=1e-12,
                                      fatol=1e-16, adaptive=True))
            v = coverval(r.x)
            P("  sc=%.1e t=%d : %.12f -> %.12f   (%+.3e vs start)" % (sc, t, coverval(xs), v, v-coverval(xs)))
            if v < best[0]-1e-14:
                best = (v, r.x.copy()); P("      *** new best")
    P("")
    P("BEST covering radius = %.17f   (candidate value %.17f, improvement %+.3e)"
      % (best[0], R0, best[0]-R0))
    Cb, Hb = unpack(best[1])
    P("best multiset distance to candidate = %.3e" % multiset_diff(np.vstack([Cb, Hb]), C0))
    with open(os.path.join(OUT, "p17_minimisation.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
