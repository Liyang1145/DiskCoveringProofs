"""Exact vertex structure of the Voronoi diagram of the saved candidate.

For every switch (finest Voronoi vertex at distance <= r from its sites),
list the cells meeting there, their angular positions around the vertex, and
the cell angles measured through that vertex.  Then test the closure identity
in the form
    (cell angle of ring k) + (cell angle of ring k+1) + (two hub angles) = 2 pi
and identify which angles the closure equation needs.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Voronoi
ROOT = Path(__file__).resolve().parents[3]
raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
c = a[rings+hubs]
vor = Voronoi(c)
m = len(vor.vertices)
print('Voronoi vertices (finite):', m)
regs = vor.regions
# map: for each site, its region
print()
for k in range(9):
    # the switch vertex closest to the pair (k,k+1) on |x|=1
    P = None; best = None
    for t, x in enumerate(vor.vertices):
        if t < 0: continue
        d = np.linalg.norm(x - c[k])
        if abs(d - np.linalg.norm(x - c[(k+1) % 9])) < 1e-9 and np.linalg.norm(x) < 1.001:
            if P is None or np.linalg.norm(x) > np.linalg.norm(P):
                P = x
    d = np.array([np.linalg.norm(P-q) for q in c])
    near = list(np.argsort(d))[:6]
    print('switch S_%d at (%.6f,%.6f) |S|=%.9f' % (k, P[0], P[1], np.linalg.norm(P)))
    print('   nearest:', [(int(i), round(float(d[i]), 9)) for i in near[:4]])
    # angular order and gapanalysis
    angs = sorted([(math.atan2((c[i]-P)[1], (c[i]-P)[0]) % (2*math.pi), int(i)) for i in near[:4]])
    print('   angular order:', [(round(math.degrees(t[0]), 4), t[1]) for t in angs])
    for t in range(4):
        a1, i1 = angs[t]; a2, i2 = angs[(t+1) % 4]
        print('      gap %2d -> %2d : %8.4f deg  (%.6f rad)' % (i1, i2, math.degrees((a2-a1) % (2*math.pi)), (a2-a1) % (2*math.pi)))
    print('   sum of 4 gaps =', sum((angs[(t+1) % 4][0]-angs[t][0]) % (2*math.pi) for t in range(4)))
