"""Print the exact switch table for the saved candidate and test THREE candidate
angle identities, so the correct one is determined unambiguously."""
import numpy as np, math, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
R = 0.38
raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
c = a[rings+hubs]
print('site angles (deg) and norms:')
for i in range(11):
    print('  c%-2d angle %8.4f  |c| %.9f' % (i, math.degrees(math.atan2(c[i, 1], c[i, 0])) % 360, np.linalg.norm(c[i])))

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
        lst = list(np.argsort(d))
        if set(lst[:2]) == {k, (k+1) % 9}:
            sw[k] = x
print()
print('switch table (pair, angle deg, radius):')
for k in range(9):
    x = sw[k]
    print('  S_%d pair(%d,%d) angle %8.4f radius %.9f' %
          (k, k, (k+1) % 9, math.degrees(math.atan2(x[1], x[0])) % 360, np.linalg.norm(x-c[k])))
# sort by angle to get cyclic order and widths
order = sorted(range(9), key=lambda k: math.atan2(sw[k][1], sw[k][0]) % (2*math.pi))
th = [math.atan2(sw[k][1], sw[k][0]) % (2*math.pi) for k in order]
w = [(th[(m+1) % 9]-th[m]) % (2*math.pi) for m in range(9)]
print()
print('cyclic order:', order)
print('widths:', np.round(w, 9), 'sum', sum(w))
print('arc owner at each arc midpoint:', [int(np.argmin([np.linalg.norm(np.array([math.cos((th[m]+w[m]/2) % (2*math.pi)), math.sin((th[m]+w[m]/2) % (2*math.pi))])-q) for q in c])) for m in range(9)])
