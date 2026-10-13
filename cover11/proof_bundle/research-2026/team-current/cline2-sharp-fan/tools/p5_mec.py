# -*- coding: utf-8 -*-
"""P5: exact MEC of each hub's assigned tips; identify the supporting triple; and
the hub-centred geometry of the tight tips."""
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
ring = sorted(ring); hub = sorted(hub)
INFO = {j: dict(b=mod[j], t=(mp.asin(R/mod[j]) if mod[j] >= R else mp.mpf(0)),
                phi=mp.atan2(C[j][1], C[j][0])) for j in range(11)}
order = sorted(ring, key=lambda j: INFO[j]['phi'])

def circum(h, i, j):
    ax, ay = C[h]; bx, by = C[i]; cx, cy = C[j]
    d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
    a2 = ax*ax+ay*ay; b2 = bx*bx+by*by; c2 = cx*cx+cy*cy
    ux = (a2*(by-cy)+b2*(cy-ay)+c2*(ay-by))/d
    uy = (a2*(cx-bx)+b2*(ax-cx)+c2*(bx-ax))/d
    return (ux, uy), mp.sqrt((ux-ax)**2+(uy-ay)**2)

P("hub Voronoi cells, assigned tips, and MEC")
for h in hub:
    tips = []
    for k in range(9):
        i = order[k]; j = order[(k+1) % 9]
        cand = []
        for hh in hub:
            p, rr = circum(hh, i, j)
            cand.append((rr, hh, p))
        cand.sort()
        rr, hh, p = cand[0]
        if hh == h:
            tips.append((i, j, p, mp.sqrt((p[0]-C[h][0])**2+(p[1]-C[h][1])**2)))
    P("")
    P("hub %d at (%s, %s), |h| = %s" % (h, mp.nstr(C[h][0], 12), mp.nstr(C[h][1], 12),
                                        mp.nstr(INFO[h]['b'], 12)))
    for i, j, p, dh in tips:
        P("   tip(%2d,%2d) = (%s, %s)   |tip|=%s  |tip-h|=%s  (|tip-h|-R=%+.6e)"
          % (i, j, mp.nstr(p[0], 15), mp.nstr(p[1], 15),
             mp.nstr(mp.sqrt(p[0]**2+p[1]**2), 15), mp.nstr(dh, 15), dh-R))
    # MEC (brute force 2 and 3 supports)
    n = len(tips)
    best = None
    for a in range(n):
        for b in range(a+1, n):
            m = ((tips[a][2][0]+tips[b][2][0])/2, (tips[a][2][1]+tips[b][2][1])/2)
            rad = mp.sqrt((tips[a][2][0]-tips[b][2][0])**2+(tips[a][2][1]-tips[b][2][1])**2)/2
            if all(mp.sqrt((p[0]-m[0])**2+(p[1]-m[1])**2) <= rad + mp.mpf(10)**-30 for (_, _, p, _) in tips):
                if best is None or rad < best[0]:
                    best = (rad, m, ("2pts", tips[a][0], tips[a][1], tips[b][0], tips[b][1]))
    for a in range(n):
        for b in range(a+1, n):
            for c in range(b+1, n):
                A, B, Cc = tips[a][2], tips[b][2], tips[c][2]
                d = 2*(A[0]*(B[1]-Cc[1])+B[0]*(Cc[1]-A[1])+Cc[0]*(A[1]-B[1]))
                if abs(d) < mp.mpf(10)**-40:
                    continue
                a2 = A[0]**2+A[1]**2; b2 = B[0]**2+B[1]**2; c2 = Cc[0]**2+Cc[1]**2
                ux = (a2*(B[1]-Cc[1])+b2*(Cc[1]-A[1])+c2*(A[1]-B[1]))/d
                uy = (a2*(Cc[0]-B[0])+b2*(A[0]-Cc[0])+c2*(B[0]-A[0]))/d
                m = (ux, uy); rad = mp.sqrt((ux-A[0])**2+(uy-A[1])**2)
                if all(mp.sqrt((p[0]-m[0])**2+(p[1]-m[1])**2) <= rad + mp.mpf(10)**-30 for (_, _, p, _) in tips):
                    if best is None or rad < best[0]:
                        best = (rad, m, ("3pts", tips[a][0:2], tips[b][0:2], tips[c][0:2]))
    P("   >>> MEC = %s  (MEC - R = %+.9e)  centre (%s, %s)  supports %s"
      % (mp.nstr(best[0], 20), best[0]-R, mp.nstr(best[1][0], 12), mp.nstr(best[1][1], 12),
         best[2]))
    P("   >>> |hub - MECcentre| = %s" % mp.nstr(mp.sqrt((C[h][0]-best[1][0])**2+(C[h][1]-best[1][1])**2), 12))
    # verify that the hub disk of radius R covers all tips of BOTH this hub and the other
    for hh in hub:
        mx = max(mp.sqrt((p[0]-C[hh][0])**2+(p[1]-C[hh][1])**2) for (_, _, p, _) in tips)
        P("   max over this hub's tips of dist to hub %d = %s (R=%s)" % (hh, mp.nstr(mx, 15), mp.nstr(R, 15)))

with open(os.path.join(OUT, "p5_mec.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
