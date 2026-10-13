"""Verify the exact identity  (cell cone angle at P_i) = pi + w/2 + 2b_i,
where w = w_i + w_{i+1} and 2b_i = angle at P_i between the two ring sites.
Also identify which "angle at P_i" the closure formula uses."""
import numpy as np, math, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
R = 0.38
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

S = []; 
for k in range(9):
    cand = []
    for x in cell_crossings(c, k):
        d = np.array([np.linalg.norm(x-q) for q in c])
        if set(list(np.argsort(d))[:2]) == {k, (k+1) % 9}: cand.append(x)
    S.append(cand[0])
S = np.array(S)
th = [math.atan2(x[1], x[0]) % (2*math.pi) for x in S]
order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
w = np.array([(ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)])

def angle(u, v): return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))

print(' i   w_i+w_{i+1}  |  cellangle(int)  pi+w/2+2b  2b(apex)  T+L+2b+w/2-pi  sidecheck')
for k in range(9):
    i, j = k, (k+1) % 9
    P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
    apex = angle(c[i]-P, c[j]-P)
    wsum = w[order.index((k-1) % 9)] + w[order.index(k)]
    # interior cell "cone" angle at P_k = angle between ray to P_{k-1} and ray to P_{k+1}
    cone = angle(Pm-P, Pp-P)
    T = angle(Pm-P, c[i]-P); L = angle(c[j]-P, Pp-P)
    pred = math.pi + wsum/2 + apex
    resid = T + L + apex + wsum/2 - math.pi
    print('%2d %9.6f | %12.6f %12.6f %9.6f  %+.2e   |cone-pred|=%.2e' %
          (k, wsum, cone, pred, apex, resid, abs(cone-pred)))
