# -*- coding: utf-8 -*-
"""P4: angles at the hub, arc geometry, and per-hub tight-set structure."""
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

P("=== angular positions of tips as seen from each hub (argument in hub-centred frame) ===")
for h in hub:
    P("hub %d at (%s, %s), |h|=%s" % (h, mp.nstr(C[h][0], 12), mp.nstr(C[h][1], 12),
                                      mp.nstr(INFO[h]['b'], 12)))
    rows = []
    for k in range(9):
        i = order[k]; j = order[(k+1) % 9]
        cand = []
        for hh in hub:
            p, rr = circum(hh, i, j)
            cand.append((rr, hh, p))
        cand.sort()
        rr, hh, p = cand[0]
        if hh != h:
            continue
        ang = mp.atan2(p[1]-C[h][1], p[0]-C[h][0])
        rows.append((i, j, rr, p, ang))
    rows.sort(key=lambda z: z[4])
    prev = None
    for i, j, rr, p, ang in rows:
        d = "" if prev is None else "  dtheta=%s" % mp.nstr(ang-prev, 10)
        P("   (%2d,%2d)  rho-R=%+.9f  theta=%+.9f  (theta/2pi=%.9f)%s"
          % (i, j, rr-R, ang, ang/(2*mp.pi), d))
        prev = ang
    P("")

P("=== ring-level data in the hub-0 frame: angle of ring site as seen from hub ===")
for h in hub:
    P("hub %d:" % h)
    for j in order:
        v = (C[j][0]-C[h][0], C[j][1]-C[h][1])
        dj = mp.sqrt(v[0]**2+v[1]**2)
        P("   ring %2d: |c_j-h|=%s  arg_h=%+.9f  |c_j|=%s  t_j=%s"
          % (j, mp.nstr(dj, 12), mp.atan2(v[1], v[0]), mp.nstr(INFO[j]['b'], 12),
             mp.nstr(INFO[j]['t'], 12)))

P("")
P("=== exact tight ledger (|rho_tip - R| < 1e-20) ===")
tight = []
for h in hub:
    for k in range(9):
        i = order[k]; j = order[(k+1) % 9]
        cand = []
        for hh in hub:
            p, rr = circum(hh, i, j)
            cand.append((rr, hh, p))
        cand.sort()
        rr, hh, p = cand[0]
        if abs(rr-R) < mp.mpf(10)**-20:
            tight.append((h, i, j, rr-R, mp.atan2(p[1]-C[h][1], p[0]-C[h][0])))
for x in tight:
    P("   hub %d rings(%2d,%2d)  rho-R=%s  theta=%+.9f" % (x[0], x[1], x[2], mp.nstr(x[3], 3), x[4]))
P("   total tight tips = %d" % len(tight))

P("")
P("=== symmetric structure check: reflection axis ===")
# candidate seems symmetric about the vertical axis; test pairing
ax = mp.pi/2
P("  phi_j + phi_{j'} vs pi (pairs about the pi/2 axis):")
pairs = [(1,1),(3,4),(5,6),(7,8),(9,10),(0,2)]
for a, b in pairs:
    s = INFO[a]['phi'] + INFO[b]['phi']
    P("     (%2d,%2d): phi_a+phi_b = %s ; pi - (sum) = %s" % (a, b, mp.nstr(s, 18), mp.nstr(mp.pi-s, 10)))
P("  moduli equality: b_a - b_b")
for a, b in pairs:
    P("     (%2d,%2d): %s" % (a, b, mp.nstr(INFO[a]['b']-INFO[b]['b'], 10)))

with open(os.path.join(OUT, "p4_hub_angles.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
