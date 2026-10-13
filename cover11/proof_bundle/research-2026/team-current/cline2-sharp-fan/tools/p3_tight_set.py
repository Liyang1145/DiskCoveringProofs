# -*- coding: utf-8 -*-
"""P3: TIGHT SET + local optimality structure of the saved candidate.

For every tip (Voronoi vertex of hub h with rings i,j) compute
   rho_tip - R,   |tip-h| - R,   angle subtended at h by (c_i,c_j),
   angle at the ring i.
Also: Jacobian rank of the tight set (numeric), and the separator geometry.
"""
import os, sys, json
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

def circum(h, i, j):
    ax, ay = C[h]; bx, by = C[i]; cx, cy = C[j]
    d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
    a2 = ax*ax+ay*ay; b2 = bx*bx+by*by; c2 = cx*cx+cy*cy
    ux = (a2*(by-cy)+b2*(cy-ay)+c2*(ay-by))/d
    uy = (a2*(cx-bx)+b2*(ax-cx)+c2*(bx-ax))/d
    return (ux, uy), mp.sqrt((ux-ax)**2+(uy-ay)**2)

P("=== TIGHT / SLACK LEDGER, all 18 (hub, ring-pair) tip candidates ===")
P("%-4s %-10s %-16s %-16s %-18s %-18s" %
  ("hub", "rings", "|tip|", "rho_tip-R", "ang at hub (rad)", "ang at hub/2pi"))
recs = []
for h in hub:
    for ki in range(len(ring)):
        for kj in range(ki+1, len(ring)):
            i = ring[ki]; j = ring[kj]
            p, rr = circum(h, i, j)
            nrm = mp.sqrt(p[0]**2+p[1]**2)
            if nrm >= 1:
                continue
            ui = ((C[i][0]-C[h][0])*(p[0]-C[h][0])+(C[i][1]-C[h][1])*(p[1]-C[h][1]))/ \
                 (mp.sqrt((C[i][0]-C[h][0])**2+(C[i][1]-C[h][1])**2)*rr)
            uj = ((C[j][0]-C[h][0])*(p[0]-C[h][0])+(C[j][1]-C[h][1])*(p[1]-C[h][1]))/ \
                 (mp.sqrt((C[j][0]-C[h][0])**2+(C[j][1]-C[h][1])**2)*rr)
            ang = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), ui*uj+mp.sqrt(1-ui*ui)*mp.sqrt(1-uj*uj)*0)))
            # safer: use atan2 of cross/dot
            v1 = (C[i][0]-C[h][0], C[i][1]-C[h][1])
            v2 = (C[j][0]-C[h][0], C[j][1]-C[h][1])
            cross = v1[0]*v2[1]-v1[1]*v2[0]
            dot = v1[0]*v2[0]+v1[1]*v2[1]
            ang = abs(mp.atan2(cross, dot))
            recs.append((h, i, j, p, rr, nrm, ang))
            P("%-4d %-10s %-16s %-16s %-18s %-18s" %
              (h, "(%2d,%2d)" % (i, j), mp.nstr(nrm, 15), mp.nstr(rr-R, 6),
               mp.nstr(ang, 15), mp.nstr(ang/(2*mp.pi), 15)))

P("")
P("=== which tip is the argmax of |tip - h| for each hub ===")
for h in hub:
    mine = [r for r in recs if r[0] == h]
    mine.sort(key=lambda r: -r[4])
    P("hub %d: max circumradius tips:" % h)
    for r in mine[:6]:
        P("    rings(%2d,%2d)  rho-R=%+.9f  arg=%.9f" %
          (r[1], r[2], r[4]-R, mp.atan2(r[3][1], r[3][0])))

P("")
P("=== the MEC of tips within each hub's Voronoi cell ===")
# hub cell = set of tips nearest THIS hub (by circumradius), i.e. assigned tips
P("(assignment by smaller circumradius, as in p2)")
assign = {}
for h in hub:
    for k in range(9):
        i = ring[k]; j = ring[(k+1) % 9]
        cand = []
        for hh in hub:
            p, rr = circum(hh, i, j)
            cand.append((rr, hh, p))
        cand.sort()
        assign[(i, j)] = cand[0]
for h in hub:
    pts = [p for (pr), (rr, hh, p) in assign.items() if hh == h]
    P("  hub %d: %d tips" % (h, len(pts)))
    # exact MEC by brute force over 2 and 3 point subsets
    best = None
    n = len(pts)
    for a in range(n):
        for b in range(a+1, n):
            m = ((pts[a][0]+pts[b][0])/2, (pts[a][1]+pts[b][1])/2)
            rad = mp.sqrt((pts[a][0]-pts[b][0])**2+(pts[a][1]-pts[b][1])**2)/2
            if all(mp.sqrt((p[0]-m[0])**2+(p[1]-m[1])**2) <= rad + mp.mpf(10)**-40 for p in pts):
                if best is None or rad < best[0]:
                    best = (rad, m, ("2", a, b))
    for a in range(n):
        for b in range(a+1, n):
            for c in range(b+1, n):
                A, B, Cc = pts[a], pts[b], pts[c]
                d = 2*(A[0]*(B[1]-Cc[1])+B[0]*(Cc[1]-A[1])+Cc[0]*(A[1]-B[1]))
                if abs(d) < mp.mpf(10)**-40:
                    continue
                a2 = A[0]**2+A[1]**2; b2 = B[0]**2+B[1]**2; c2 = Cc[0]**2+Cc[1]**2
                ux = (a2*(B[1]-Cc[1])+b2*(Cc[1]-A[1])+c2*(A[1]-B[1]))/d
                uy = (a2*(Cc[0]-B[0])+b2*(A[0]-Cc[0])+c2*(B[0]-A[0]))/d
                m = (ux, uy); rad = mp.sqrt((ux-A[0])**2+(uy-A[1])**2)
                if all(mp.sqrt((p[0]-m[0])**2+(p[1]-m[1])**2) <= rad + mp.mpf(10)**-40 for p in pts):
                    if best is None or rad < best[0]:
                        best = (rad, m, ("3", a, b, c))
    if best:
        P("    MEC radius = %s (MEC-R = %+.9f)  centre=(%s,%s)  type=%s"
          % (mp.nstr(best[0], 18), best[0]-R, mp.nstr(best[1][0], 12),
             mp.nstr(best[1][1], 12), best[2]))
    # supporting points
    sup = [k for k, p in enumerate(pts)
           if abs(mp.sqrt((p[0]-best[1][0])**2+(p[1]-best[1][1])**2) - best[0]) < mp.mpf(10)**-25]
    P("    supporting tips indices %s ; tips:" % sup)
    for k in sup:
        P("        tip %d = (%s, %s) |tip|=%s" % (k, mp.nstr(pts[k][0], 15),
                                                  mp.nstr(pts[k][1], 15),
                                                  mp.nstr(mp.sqrt(pts[k][0]**2+pts[k][1]**2), 15)))

P("")
P("=== separator (perpendicular bisector of the two hubs) ===")
h0, h1 = hub
mid = ((C[h0][0]+C[h1][0])/2, (C[h0][1]+C[h1][1])/2)
nv = (C[h1][0]-C[h0][0], C[h1][1]-C[h0][1])
nrm = mp.sqrt(nv[0]**2+nv[1]**2)
P("  mid = (%s, %s) ; |mid| = %s" % (mp.nstr(mid[0], 15), mp.nstr(mid[1], 15),
                                     mp.nstr(mp.sqrt(mid[0]**2+mid[1]**2), 15)))
P("  hub-hub distance = %s = 2R*%s" % (mp.nstr(nrm, 15), mp.nstr(nrm/(2*R), 15)))
# distance of hit points
for k in range(9):
    i = ring[k]; j = ring[(k+1) % 9]
    rr, hh, p = assign[(i, j)]
    sgn = ((p[0]-mid[0])*nv[0] + (p[1]-mid[1])*nv[1])
    P("    tip(%2d,%2d) assigned hub %d : signed separator dist = %s  (|tip|=%.6f)"
      % (i, j, hh, mp.nstr(sgn/nrm, 10), mp.nstr(mp.sqrt(p[0]**2+p[1]**2), 8)))

with open(os.path.join(OUT, "p3_tight_set.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
