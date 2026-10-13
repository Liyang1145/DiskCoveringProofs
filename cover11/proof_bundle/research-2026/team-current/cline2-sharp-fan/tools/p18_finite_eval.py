# -*- coding: utf-8 -*-
"""P18: EXACT FINITE evaluator for the covering radius of a q0 configuration.

Object: 9 rings c_0..c_8 + 2 hubs h_1,h_2, radius R; q0 fan class (each ring-ring edge
belongs to exactly one hub's fan, the two hubs' blocks are complementary arcs).
Claim (finite criterion, to be justified): for such a configuration the covering radius
    R_cov = max_{x in D} min_k |x-c_k|
is attained in the FINITE set
    S = 9 switches  P_i  (crossings on bd D of consecutive rings)
      U 9 tips     T_i  (circumcentre of (hub(i), ring_i, ring_{i+1}))
because (a) the boundary is covered by the rings alone in this class, so no point of
bd D determines the max unless it IS a switch, and (b) every other local maximum of the
distance-to-nearest-site function is a Voronoi vertex, i.e. a tip.
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
RING = [1, 3, 4, 5, 6, 7, 8, 9, 10]
HUB = [0, 2]
lines = []
def P(s=""):
    lines.append(s); print(s)

mod = np.linalg.norm(C0, axis=1)
psi = np.arctan2(C0[:, 1], C0[:, 0])
order = sorted(RING, key=lambda j: psi[j])
P("ring order %s" % order)


# ---- the true maximum from a dense polar grid (reference) ----
NR, NTH = 1200, 6000
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)
d = np.linalg.norm(PTS[:, None, :]-C0[None, :, :], axis=2).min(axis=1)
i = int(np.argmax(d))
from scipy.optimize import minimize
def neg(p):
    return -float(np.min(np.linalg.norm(C0-p, axis=1))) if p[0]**2+p[1]**2 <= 1 else 1e4*(p[0]**2+p[1]**2-1)
res = minimize(neg, PTS[i], method='Nelder-Mead', options=dict(xatol=1e-15, fatol=1e-17, maxiter=8000))
P("reference (dense grid + refine) covering radius = %.17f" % (-res.fun))
P("argmax = (%.12f, %.12f), |x| = %.15f" % (res.x[0], res.x[1], np.linalg.norm(res.x)))


def tip(h, i, j):
    a, b, c = C0[h], C0[i], C0[j]
    dd = 2*(a[0]*(b[1]-c[1])+b[0]*(c[1]-a[1])+c[0]*(a[1]-b[1]))
    a2 = a@a; b2 = b@b; c2 = c@c
    ux = (a2*(b[1]-c[1])+b2*(c[1]-a[1])+c2*(a[1]-b[1]))/dd
    uy = (a2*(c[0]-b[0])+b2*(a[0]-c[0])+c2*(b[0]-a[0]))/dd
    return np.array([ux, uy])


def switch(i, j):
    a, b = C0[i], C0[j]
    dd = np.linalg.norm(a-b)
    m = (a+b)/2
    hh = math.sqrt(max(R0*R0-dd*dd/4, 0.0))
    perp = np.array([-(b-a)[1], (b-a)[0]])/dd
    p1 = m+hh*perp; p2 = m-hh*perp
    return p1 if np.linalg.norm(p1) <= np.linalg.norm(p2) else p2


P("")
P("=== the 18-point set S and their nearest-site distances ===")
S = []
for k in range(9):
    a = order[k]; b = order[(k+1) % 9]
    p = switch(a, b); S.append(("SW(%2d,%2d)" % (a, b), p))
    best = min(((np.linalg.norm(p-C0[h]), h) for h in HUB))
    chosen = None
    for h in HUB:
        t = tip(h, a, b)
        rr = np.linalg.norm(t-C0[h])
        if chosen is None or rr < chosen[1]:
            chosen = (h, rr, t)
    if chosen[1] <= R0+1e-9:
        S.append(("TIP(%2d,%2d|h%d)" % (a, b, chosen[0]), chosen[2]))
mx = 0.0; arg = None
for nm, p in S:
    v = float(np.min(np.linalg.norm(C0-p, axis=1)))
    if v > mx:
        mx = v; arg = nm
    P("   %-18s |x|=%9.6f  min_k |x-c_k| = %.15f  (diff to R = %+.3e)"
      % (nm, np.linalg.norm(p), v, v-R0))
P("")
P("max over S of min_k |x-c_k| = %.17f   at %s" % (mx, arg))
P("reference max                = %.17f" % (-res.fun))
P("difference                   = %+.3e" % (mx-(-res.fun)))
P("")
P("=> finite-set maximum reproduces the true covering radius to %.1e" % abs(mx-(-res.fun)))
with open(os.path.join(OUT, "p18_finite_eval.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines)+"\n")
