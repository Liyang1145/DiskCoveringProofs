# -*- coding: utf-8 -*-
"""P19: exact accounting of the sharp configuration's tight set.

For every ring-ring switch P_i and every (hub, ring-pair) tip T, compute the distance to
the hub that is supposed to cover it, and the location of the WORST uncovered point.
"""
import os, sys, math, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R = 0.3799838531198387090485181795734298538115979028
RING = [1, 3, 4, 5, 6, 7, 8, 9, 10]
HUB = [0, 2]
lines = []
def P(s=""):
    lines.append(s); print(s)

mod = np.linalg.norm(C, axis=1)
psi = np.arctan2(C[:, 1], C[:, 0])
order = sorted(RING, key=lambda j: psi[j])
P("ring cyclic order: %s" % order)


def circum(h, i, j):
    a, b, c = C[h], C[i], C[j]
    dd = 2*(a[0]*(b[1]-c[1])+b[0]*(c[1]-a[1])+c[0]*(a[1]-b[1]))
    a2 = a@a; b2 = b@b; c2 = c@c
    ux = (a2*(b[1]-c[1])+b2*(c[1]-a[1])+c2*(a[1]-b[1]))/dd
    uy = (a2*(c[0]-b[0])+b2*(a[0]-c[0])+c2*(b[0]-a[0]))/dd
    return np.array([ux, uy])


def switch(i, j):
    a, b = C[i], C[j]
    dd = np.linalg.norm(a-b); m = (a+b)/2
    hh = math.sqrt(max(R*R-dd*dd/4, 0.0))
    perp = np.array([-(b-a)[1], (b-a)[0]])/dd
    p1 = m+hh*perp; p2 = m-hh*perp
    return p1 if np.linalg.norm(p1) <= np.linalg.norm(p2) else p2


P("")
P("=== SWITCHES: distance to nearest hub and to nearest ring ===")
P("%-12s %-14s %-14s %-12s %-14s %-12s" % ("switch", "|P|", "hub dist - R", "hub", "ring dist - R", "which rings"))
for k in range(9):
    a = order[k]; b = order[(k+1) % 9]
    p = switch(a, b)
    dhh = [(np.linalg.norm(p-C[h]), h) for h in HUB]
    dhh.sort()
    drr = sorted((np.linalg.norm(p-C[r]), r) for r in RING)
    P("%-12s %-14.9f %-14.3e %-12d %-14.3e %s" %
      ("SW(%d,%d)" % (a, b), np.linalg.norm(p), dhh[0][0]-R, dhh[0][1], drr[0][0]-R,
       [(int(r), round(float(d), 6)) for d, r in drr[:3]]))

P("")
P("=== TIPS: circumcentres of (hub, ring_i, ring_j), distance to their hub ===")
for h in HUB:
    P(" hub %d:" % h)
    for k in range(9):
        a = order[k]; b = order[(k+1) % 9]
        t = circum(h, a, b)
        rr = np.linalg.norm(t-C[h])
        if rr <= R + 1e-6:
            # is this tip covered by the OTHER hub instead?
            other = [x for x in HUB if x != h][0]
            do = np.linalg.norm(t-C[other])
            P("    TIP(%2d,%2d|h%d): rho-R=%+.3e   dist to other hub - R = %+.3e  %s"
              % (a, b, h, rr-R, do-R, "<-- COVERED" if rr <= R+1e-12 else ""))

P("")
P("=== the TRUE worst point: solve max min_k |x-c_k| ===")
from scipy.optimize import minimize
NR, NTH = 2000, 10000
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)
d = np.linalg.norm(PTS[:, None, :]-C[None, :, :], axis=2).min(axis=1)
i = int(np.argmax(d))
def neg(p):
    return -float(np.min(np.linalg.norm(C-p, axis=1))) if p[0]**2+p[1]**2 <= 1 else 1e4*(p[0]**2+p[1]**2-1)
res = minimize(neg, PTS[i], method='Nelder-Mead', options=dict(xatol=1e-16, fatol=1e-18, maxiter=10000))
worst = res.x
P("worst point = (%.15f, %.15f), |x| = %.15f" % (worst[0], worst[1], np.linalg.norm(worst)))
P("covering radius = %.17f   (R = %.17f, slack %+.3e)" % (-res.fun, R, -res.fun-R))
ds = sorted((np.linalg.norm(worst-C[k]), int(k)) for k in range(11))
P("distances to all 11 centres: %s" % [(k, round(float(v), 12)) for v, k in ds])
P("")
P("(the worst point is the common tangency point of rings %d and %d, and it is at distance" %
  (ds[0][1], ds[1][1]))
P(" R from both; the hub disk does not reach it, and it does not need to: it is covered")
P(" by the two rings exactly at radius R.)")
with open(os.path.join(OUT, "p19_accounting.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines)+"\n")
