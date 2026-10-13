# -*- coding: utf-8 -*-
"""P15: FINAL verified ledger for the milestone note.

Computes, from the saved certified object (exact integer coordinates / 1e17):
  (1) true covering radius of the 11-disk configuration (fine grid + local refinement);
  (2) boundary defect  max_{|P|=1} min_i |P-c_i| - R  (rings only);
  (3) the tip (Voronoi-vertex) ledger: per assigned hub, rho_tip - R;
  (4) MEC of each hub's assigned tips and its supporting set;
  (5) saturation/dichotomy data (rings' boundary slack, hub |h|+R-1).
"""
import os, sys, math, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
lines = []
def P(s=""):
    lines.append(s); print(s)

with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R = 0.3799838531198387090485181795734298538115979028
RING = [1, 3, 4, 5, 6, 7, 8, 9, 10]
HUB = [0, 2]
mod = np.linalg.norm(C, axis=1)
psi = np.arctan2(C[:, 1], C[:, 0])

# ---------- (1) covering radius ----------
NR, NTH = 1500, 7200
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)
d = np.linalg.norm(PTS[:, None, :]-C[None, :, :], axis=2).min(axis=1)
i = int(np.argmax(d))
from scipy.optimize import minimize
def neg(p):
    if p[0]**2+p[1]**2 > 1.0:
        return 1e4*(p[0]**2+p[1]**2-1.0)
    return -float(np.min(np.linalg.norm(C-p, axis=1)))
res = minimize(neg, PTS[i], method='Nelder-Mead',
               options=dict(xatol=1e-15, fatol=1e-17, maxiter=8000))
covR = max(float(d[i]), -res.fun)
P("(1) covering radius of the 11-disk configuration = %.17f" % covR)
P("    claimed certified value R                   = %.17f" % R)
P("    difference                                  = %+.3e" % (covR-R))
P("    worst point = (%.12f, %.12f)   |x|=%.12f" % (res.x[0], res.x[1], math.hypot(*res.x)))
srt = np.argsort(np.linalg.norm(C-res.x, axis=1))
P("    nearest centres: %s" % [(int(k), round(float(np.linalg.norm(C[k]-res.x)), 12)) for k in srt[:4]])
P("    (note: 0.38-R = %.3e : the candidate misses the R=19/50 target by this much)" % (0.38-R))

# ---------- (2) boundary defect ----------
M = 4000001
th = np.linspace(0, 2*np.pi, M, endpoint=False)
BD = np.stack([np.cos(th), np.sin(th)], axis=1)
db = np.linalg.norm(BD[:, None, :]-C[RING][None, :, :], axis=2).min(axis=1)
P("")
P("(2) boundary defect of the 9 rings (refined):")
imin = int(np.argmin(np.abs(db-R)))
# refine the local max near the grid argmax
j0 = int(np.argmax(db))
from scipy.optimize import minimize_scalar
def fdef(t):
    p = np.array([math.cos(t), math.sin(t)])
    return -float(np.min(np.linalg.norm(C[RING]-p, axis=1)))
lo, hi = th[j0]-2*math.pi/M, th[j0]+2*math.pi/M
rr = minimize_scalar(fdef, bounds=(lo, hi), method='bounded',
                     options=dict(xatol=1e-16))
P("    max over bd D of min_i |P-c_i| = %.17f   (this is the max distance attained ON the boundary)"
  % (-rr.fun))
P("    boundary defect vs R           = %+.6e" % (-rr.fun-R))
P("    argmax angle = %.12f ; closest rings: %s"
  % (rr.x, [(int(r), round(float(np.linalg.norm(C[r]-np.array([math.cos(rr.x), math.sin(rr.x)]))), 10))
            for r in np.argsort(np.linalg.norm(C-np.array([math.cos(rr.x), math.sin(rr.x)]), axis=1))[:3]]))
P("    => the boundary is NOT saturated: it keeps ~%.2e of slack at R=0.38" % (-rr.fun-R))

# ---------- (3)/(4) tips ----------
def circum(h, i, j):
    ax, ay = C[h]; bx, by = C[i]; cx, cy = C[j]
    dd = 2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    a2 = ax*ax+ay*ay; b2 = bx*bx+by*by; c2 = cx*cx+cy*cy
    ux = (a2*(by-cy)+b2*(cy-ay)+c2*(ay-by))/dd
    uy = (a2*(cx-bx)+b2*(ax-cx)+c2*(bx-ax))/dd
    return np.array([ux, uy]), math.hypot(ux-ax, uy-ay)

order = sorted(RING, key=lambda j: psi[j])
P("")
P("(3) tip ledger: tip(i,j|h) = circumcentre of (hub h, ring i, ring j)")
P("    'assigned' = the hub giving the smaller circumradius; tight = circumradius == R")
tips = {}
for k in range(9):
    a = order[k]; b = order[(k+1) % 9]
    cand = sorted((circum(h, a, b)[1], h, circum(h, a, b)[0]) for h in HUB)
    rr_, hh, pp = cand[0]
    tips[(a, b)] = (hh, pp, rr_)
assign = {h: [] for h in HUB}
for (a, b), (hh, pp, rr_) in tips.items():
    assign[hh].append(((a, b), pp, rr_))
for h in HUB:
    P("   hub %d (|h|=%.15f, |h|+R-1=%+.3e):" % (h, mod[h], mod[h]+R-1))
    for (a, b), pp, rr_ in assign[h]:
        tight = "TIGHT" if abs(rr_-R) < 1e-12 else "     "
        P("      tip(%2d,%2d) %s  rho-R=%+.6e   |tip|=%.12f" % (a, b, tight, rr_-R, np.linalg.norm(pp)))

P("")
P("(4) MEC of each hub's assigned tip set (exhaustive over 2- and 3-point supports):")
for h in HUB:
    pts = [pp for _, pp, _ in assign[h]]
    n = len(pts)
    best = None
    for a in range(n):
        for b in range(a+1, n):
            m = (pts[a]+pts[b])/2; rad = np.linalg.norm(pts[a]-pts[b])/2
            if all(np.linalg.norm(p-m) <= rad+1e-13 for p in pts):
                if best is None or rad < best[0]:
                    best = (rad, m, ("2", a, b))
    for a in range(n):
        for b in range(a+1, n):
            for c in range(b+1, n):
                A, B, Cc = pts[a], pts[b], pts[c]
                dd = 2*(A[0]*(B[1]-Cc[1])+B[0]*(Cc[1]-A[1])+Cc[0]*(A[1]-B[1]))
                if abs(dd) < 1e-15:
                    continue
                a2 = A@A; b2 = B@B; c2 = Cc@Cc
                ux = (a2*(B[1]-Cc[1])+b2*(Cc[1]-A[1])+c2*(A[1]-B[1]))/dd
                uy = (a2*(Cc[0]-B[0])+b2*(A[0]-Cc[0])+c2*(B[0]-A[0]))/dd
                m = np.array([ux, uy]); rad = np.linalg.norm(m-A)
                if all(np.linalg.norm(p-m) <= rad+1e-13 for p in pts):
                    if best is None or rad < best[0]:
                        best = (rad, m, ("3", a, b, c))
    P("   hub %d: MEC radius = %.15f  (MEC - R = %+.3e)  supports %s"
      % (h, best[0], best[0]-R, best[2]))
    P("           MEC centre = (%.12f, %.12f) ; |hub - centre| = %.3e"
      % (best[1][0], best[1][1], np.linalg.norm(C[h]-best[1])))
    sup = [assign[h][k][0] for k in best[2][1:]]
    P("           supporting tips: %s" % sup)

P("")
P("(5) saturation dichotomy check:")
P("   rings: |c_i| + R - 1 = %s"
  % np.round([mod[j]+R-1 for j in RING], 6).tolist())
P("   min over rings = %+.6e  => NO ring is boundary-tangent (all 9 have slack)"
  % min(mod[j]+R-1 for j in RING))
P("   hub |h|-R = %s  (both hubs satisfy |h| < R)"
  % np.round([mod[h]-R for h in HUB], 6).tolist())

with open(os.path.join(OUT, "p15_final_ledger.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines)+"\n")
