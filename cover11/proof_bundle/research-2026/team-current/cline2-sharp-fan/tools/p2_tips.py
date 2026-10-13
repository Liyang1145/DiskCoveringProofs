# -*- coding: utf-8 -*-
"""P2: tips = true Voronoi vertex of (hub, ring_i, ring_j); verify equioscillation.

tip(i,j,h) = point p with |p-c_i|=|p-c_j|=|p-h| (the circumcentre of the triple).
Print tip, |tip|, dist to hub (=circumradius), and the fan-closure data.
"""
import os, sys
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import load_object, classify, HERE

mp.mp.dps = 60
OUT = os.path.join(HERE, os.pardir, "out")
lines = []
def P(s=""):
    lines.append(s); print(s)

C, R, mp = load_object()
ring, hub, mod = classify(C, R)
info = {}
for j in range(11):
    info[j] = dict(b=mod[j], t=(mp.asin(R/mod[j]) if mod[j] > R else mp.mpf(0)),
                   phi=mp.atan2(C[j][1], C[j][0]))
order = sorted(ring, key=lambda j: info[j]['phi'])

def circumcentre(h, i, j):
    """circumcentre of three sites (returns (p, radius))."""
    ax, ay = C[h]; bx, by = C[i]; cx, cy = C[j]
    d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
    if abs(d) < mp.mpf(10)**-50:
        return None, None
    a2 = ax*ax+ay*ay; b2 = bx*bx+by*by; c2 = cx*cx+cy*cy
    ux = (a2*(by-cy) + b2*(cy-ay) + c2*(ay-by))/d
    uy = (a2*(cx-bx) + b2*(ax-cx) + c2*(bx-ax))/d
    p = (ux, uy)
    r = mp.sqrt((ux-ax)**2 + (uy-ay)**2)
    return p, r

P("tips: true circumcentre of (hub, ring_i, ring_j); radius vs R")
P("%-12s %-3s %-22s %-22s %-11s %-22s %-12s" %
  ("edge", "hub", "|tip|", "radius-R", "hubdist-R", "edgechord/2", "arg(tip)"))
tips = {}
for k in range(9):
    i = order[k]; jj = order[(k+1) % 9]
    row = []
    for h in hub:
        p, rr = circumcentre(h, i, jj)
        if p is None:
            continue
        rad = mp.sqrt(p[0]**2+p[1]**2)
        dh = mp.sqrt((p[0]-C[h][0])**2 + (p[1]-C[h][1])**2)
        de = mp.sqrt((p[0]-C[i][0])**2 + (p[1]-C[i][1])**2)
        row.append((rr-R, h, p, rad, dh))
    row.sort(key=lambda z: abs(z[0]))
    for rr_m, h, p, rad, dh in row:
        P("%-12s %-3d %-22s %-22s %-11s %-22s %-12s" %
          ("(%d,%d)" % (i, jj), h, mp.nstr(rad, 18), mp.nstr(rr_m, 6),
           mp.nstr(dh-R, 6), mp.nstr(mp.sqrt((C[i][0]-C[jj][0])**2+
                                             (C[i][1]-C[jj][1])**2)/2, 18),
           mp.nstr(mp.atan2(p[1], p[0]), 14)))
    tips[(i, jj)] = row[0][2]

# also: hub-hub-ring triangles
P("")
P("hub-hub-ring triangles (h0,h1,c_u):")
for u in ring:
    p, rr = circumcentre(hub[0], hub[1], u)
    if p is None:
        continue
    P("   u=%-3d circumradius-R = %-22s |p|=%s" % (u, mp.nstr(rr-R, 6), mp.nstr(mp.sqrt(p[0]**2+p[1]**2), 12)))

# which ring-ring edges are 'owned' by which hub (nearest tip radius)
P("")
P("assigned hub per ring-ring edge (smaller tip radius):")
blocks = {h: [] for h in hub}
for k in range(9):
    i = order[k]; jj = order[(k+1) % 9]
    row = []
    for h in hub:
        p, rr = circumcentre(h, i, jj)
        row.append((rr, h, p))
    row.sort()
    blocks[row[0][1]].append(k)
    P("   (%2d,%2d) -> hub %d  (r-R=%s vs other %s)"
      % (i, jj, row[0][1], mp.nstr(row[0][0]-R, 8), mp.nstr(row[1][0]-R, 8)))
for h in hub:
    P("   hub %d owns tips at ring-order positions %s" % (h, blocks[h]))

# exactness of the tight set
P("")
tight_circ = 0
for h in hub:
    for k in range(9):
        i = order[k]; jj = order[(k+1) % 9]
        p, rr = circumcentre(h, i, jj)
        if abs(rr-R) < mp.mpf('1e-13'):
            tight_circ += 1
P("ring-ring fan triangles with circumradius == R (to 1e-13): %d / 18" % tight_circ)
hh_tight = sum(1 for u in ring
               if abs(circumcentre(hub[0], hub[1], u)[1] - R) < mp.mpf('1e-13'))
P("hub-hub fan triangles with circumradius == R (to 1e-13): %d / 9" % hh_tight)
P("rings strictly touching bd D (|c|+R == 1): %s" %
  [ (j, mp.nstr(mod[j]+R-1, 6)) for j in ring ])

with open(os.path.join(OUT, "p2_tips.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
