"""Determine, for the saved candidate, the actual Voronoi vertex structure at each
switch: which cells meet, their angular order around the switch, and the cell angles.
This decides the correct angle conventions for the closure identity."""
import numpy as np, math, json, itertools
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
c = a[rings+hubs]

def cell_crossings(points, i):
    cr = []
    for j in range(len(points)):
        if j == i: continue
        m = 0.5*(points[i]+points[j]); d = points[j]-points[i]
        nrm = np.array([d[1], -d[0]])/np.linalg.norm(d)
        t0 = -(m @ nrm); s2 = 1 - m @ m
        if s2 < 0: continue
        for sgn in (+1, -1):
            x = m + (t0 + sgn*math.sqrt(t0*t0+s2))*nrm
            di = np.linalg.norm(x-points[i]); dj = np.linalg.norm(x-points[j])
            if abs(di-dj) > 1e-9: continue
            if di - min(np.linalg.norm(x-q) for q in points) > 1e-9: continue
            if not any(np.linalg.norm(x-y) < 1e-7 for y in cr): cr.append(x)
    return cr

sw = {}
for k in range(9):
    for x in cell_crossings(c, k):
        d = np.array([np.linalg.norm(x-q) for q in c])
        if set(list(np.argsort(d))[:2]) == {k, (k+1) % 9}: sw[k] = x

for k in [5]:
    S = sw[k]
    print('switch S_%d =' % k, np.round(S, 9), '|S|=%.12f' % np.linalg.norm(S))
    dd = np.array([np.linalg.norm(S-q) for q in c])
    print('distances to sites:', np.round(dd, 9))
    near = list(np.argsort(dd))[:6]
    print('nearest sites:', [(int(i), round(float(dd[i]), 9)) for i in near])
    # for each site, the direction from S to the site and its angle
    for i in near:
        v = c[i]-S
        print('   site %2d  dir angle %8.4f deg  |dir| %.6f   dot(dir, S)=%.6f (negative => inland)'
              % (i, math.degrees(math.atan2(v[1], v[0])) % 360, np.linalg.norm(v), float(v @ S)))
    # angular order of the four nearest (the four-cell partition)
    angs = sorted([(math.degrees(math.atan2((c[i]-S)[1], (c[i]-S)[0])) % 360, int(i)) for i in near[:4]])
    print('   angular order of the 4 nearest cells:', angs)
    # gaps
    for t in range(4):
        a1, i1 = angs[t]; a2, i2 = angs[(t+1) % 4]
        print('      gap from site %d to site %d : %.4f deg' % (i1, i2, (a2-a1) % 360))
    # compare with the two candidate "apex" definitions
    c5, c6 = c[5], c[6]
    ang = lambda u, v: math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))
    print('   angle at S between c5,c6 =', ang(c5-S, c6-S))
    # ray directions to the two adjacent switches
    P4, P6 = sw[4], sw[6]
    print('   angle from (P4-S) to (c5-S) =', ang(P4-S, c5-S), ' (T)')
    print('   angle from (c6-S) to (P6-S) =', ang(c6-S, P6-S), ' (L)')
