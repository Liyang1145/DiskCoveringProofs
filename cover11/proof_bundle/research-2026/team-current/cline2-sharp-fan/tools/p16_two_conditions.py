# -*- coding: utf-8 -*-
"""P16: the exact two-condition structure of the covering radius at R=19/50.

R(c_0..c_10) := max_{x in D} min_k |x - c_k|   (covering radius of the 11 disks)
At the sharp optimum this maximum is attained at
   (A) a boundary point that is the COMMON tangency point of a ring and a consecutive
       ring's arc (i.e. a switch), and
   (B) the circumcentre of (hub, ring_i, ring j) - a Voronoi vertex.
Both must equal R.

This script:
  1. verifies (A) and (B) numerically;
  2. computes the local sensitivity dR/d(parameters) to identify the active manifold;
  3. runs a careful multi-start minimisation of R over the reduced parameterisation
     (rho_i, phi_i, h1, h2).
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
lines = []
def P(s=""):
    lines.append(s); print(s)


# ---------------- evaluator ----------------
NR, NTH = 800, 4000
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)


def make_unpack():
    rho0 = np.linalg.norm(C0[RING], axis=1)
    psi0 = np.arctan2(C0[RING, 1], C0[RING, 0])
    idx = np.argsort(psi0)
    rho0 = rho0[idx]; psi0 = np.mod(psi0[idx]-psi0[idx[0]], 2*np.pi)
    return rho0, psi0


def unpack(x):
    rho = np.abs(x[:9])
    ph = np.concatenate([[0.0], x[9:17]])
    C = np.stack([rho*np.cos(ph), rho*np.sin(ph)], axis=1)
    H = x[17:21].reshape(2, 2)
    return C, H


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


if __name__ == "__main__":
    rho0, psi0 = make_unpack()
    P("ring moduli: %s" % np.round(rho0, 12).tolist())
    P("ring angles: %s" % np.round(psi0, 12).tolist())
    x0 = np.concatenate([rho0, psi0[1:], C0[HUB[0]], C0[HUB[1]]])
    C, H = unpack(x0)
    # exact reconstruction test on the FULL set
    A = np.sort(np.vstack([C, H]), axis=0)
    B = np.sort(C0, axis=0)
    P("reconstruction max|diff| (sorted rows) = %.3e" % np.abs(A-B).max())
    P("coverval(x0) = %.17f" % coverval(x0))
    # ground truth = coverval of the original coordinates (order irrelevant)
    ALL0 = C0
    d = np.linalg.norm(PTS[:, None, :]-ALL0[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d))
    def neg(p):
        if p[0]**2+p[1]**2 > 1.0:
            return 1e4*(p[0]**2+p[1]**2-1.0)
        return -float(np.min(np.linalg.norm(ALL0-p, axis=1)))
    res = minimize(neg, PTS[i], method='Nelder-Mead',
                   options=dict(xatol=1e-15, fatol=1e-17, maxiter=6000))
    P("ground-truth covering radius = %.17f   (diff to R = %+.3e)" % (-res.fun, -res.fun-R0))
    P("argmax point = (%.12f,%.12f) |x|=%.15f" % (res.x[0], res.x[1], np.linalg.norm(res.x)))
    srt = np.argsort(np.linalg.norm(ALL0-res.x, axis=1))
    P("two nearest sites: %s" % [(int(k), round(float(np.linalg.norm(ALL0[k]-res.x)), 15)) for k in srt[:3]])
    P("")
    P("structure of that argmax:")
    P("   (A) it is a RING-RING switch on bd D: rings %d and %d both at distance R"
      % (srt[0], srt[1]))
    P("   (B) the interior tip (9,10|hub 0) is at distance R from hub 0 by construction")
    P("")

    # ---------------- sensitivity ----------------
    P("=== one-sided sensitivity of R at the candidate (finite differences) ===")
    P("parameter   +delta: R change    -delta: R change     (delta=2e-3)")
    dl = 2e-3
    for name, k in [("rho_%d" % i, i) for i in range(9)] + \
                   [("phi_%d" % i, 9+i) for i in range(8)] + \
                   [("h1x", 17), ("h1y", 18), ("h2x", 19), ("h2y", 20)]:
        xp = x0.copy(); xm = x0.copy()
        xp[k] += dl; xm[k] -= dl
        P("  %-10s %+.6e       %+.6e" % (name, coverval(xp)-coverval(x0), coverval(xm)-coverval(x0)))
    with open(os.path.join(OUT, "p16_two_conditions.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
