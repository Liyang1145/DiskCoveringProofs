"""DECISIVE check: does the C182 configuration cover D with disks of radius R_D?

R_D(C) = max_{x in D} min_i |x - c_i|  (this is what cert_bb.py proves <= claim).
If the max-min exceeds the claim, coverage by that radius FAILS.
"""
from pathlib import Path
import json, math
import numpy as np

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
C = np.array([[float(x), float(y)] for x, y in A["centers_dec17"]])
Rlit = float(A["R_float"])
print("R_float in cfg       :", repr(Rlit))
print("|c_i|                :", np.round(np.linalg.norm(C, axis=1), 12).tolist())

# exact max-min on a fine polar+cartesian grid
best = (-1, None)
N = 6000
for a in range(N+1):
    x = -1 + 2*a/N
    for b in range(N+1):
        y = -1 + 2*b/N
        if x*x+y*y > 1: continue
        d = np.min(np.hypot(C[:,0]-x, C[:,1]-y))
        if d > best[0]: best = (d, (x, y))
print("max-min on grid      :", repr(best[0]), "at", best[1])

# boundary-only
bb = (-1, None)
t = np.linspace(0, 2*np.pi, 4_000_001)
P = np.stack([np.cos(t), np.sin(t)], axis=1)
# chunked min-distance
mx = -1; arg = None
for i in range(0, len(P), 200_000):
    Q = P[i:i+200_000]
    D = np.linalg.norm(Q[:, None, :] - C[None, :, :], axis=2).min(axis=1)
    j = int(np.argmax(D))
    if D[j] > mx:
        mx = D[j]; arg = (Q[j, 0], Q[j, 1], t[i+j])
print("boundary max-min     :", repr(mx), "at", arg[0], arg[1], "theta_deg", math.degrees(arg[2]))

# Voronoi vertices (triple circumcentres) covered-inside
import itertools
best_v = (-1, None)
for i, j, k in itertools.combinations(range(12), 3):
    ax, ay = C[i]; bx, by = C[j]; cx, cy = C[k]
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < 1e-15: continue
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den
    if ux*ux+uy*uy > 1: continue
    d = float(np.min(np.hypot(C[:,0]-ux, C[:,1]-uy)))
    if d > best_v[0]: best_v = (d, (ux, uy, (i, j, k)))
print("deepest Voronoi vert :", repr(best_v[0]), "at", best_v[1])
print()
print("=> max_{x in D} min_i |x-c_i| =", max(best[0], mx, best_v[0]))
print("   certified D2 claim       = 0.3611029637445086726169202939")
print("   so coverage by radius", Rlit, ":", "OK" if max(best[0], mx) <= Rlit else "FAILS")
