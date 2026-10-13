"""Diagnostics: for the saved certified upper candidate,
 (1) covering radius decomposition (all Voronoi vertices, inside and outside D),
 (2) for each ring/switch pair: the two containment inequalities that the
     fan-triangulation ("all sites lie inside the switch polygon") requires,
 (3) the closure residual under the two sign conventions.
Everything from coordinates only.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Delaunay, ConvexHull
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def ang2(u, v):  # signed angle in (-pi,pi]
    return math.atan2(u[0]*v[1]-u[1]*v[0], float(u @ v))

def angabs(u, v):
    c = float(u @ v)/np.linalg.norm(u)/np.linalg.norm(v)
    return math.acos(max(-1, min(1, c)))

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
c = a[rings + hubs]
tri = Delaunay(c)
print('faces', len(tri.simplices))
rad = []
for f in tri.simplices:
    p = c[f]
    v = np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))
    rad.append((float(np.linalg.norm(v)), float(np.linalg.norm(v-p[0])), tuple(f)))
rad.sort(key=lambda t: -t[1])
print('top circumradii (|v|, rho_v, face):')
for t in rad[:6]: print('   |v|=%.6f rho=%.6f face=%s' % t)
print('max circumradius over faces with |v|<1 :', max(t[1] for t in rad if t[0] < 1))
print('number of faces with |v|<1 :', sum(1 for t in rad if t[0] < 1), 'of', len(rad))
print('sites with |c|<rho_v?  (Voronoi vertex inside its own site disk is fine)')

# containment inequalities for each boundary switch
print()
print('containment check: for each ring i, switches P_{i-1} (with c_{i-1}) and P_i (with c_{i+1})')
def switch_pair(i, j):
    m = 0.5*(c[i]+c[j]); d = c[j]-c[i]; n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    best = None
    for sgn in (+1, -1):
        x = m + (t0 + sgn*math.sqrt(t0*t0+s2))*n
        if np.linalg.norm(x-c[i]) - min(np.linalg.norm(x-q) for q in c) < 1e-9:
            best = x
    return best
S = [switch_pair(k, (k+1) % 9) for k in range(9)]
worst = 0
for i in range(9):
    Pm = S[(i-1) % 9]; Pp = S[i]
    x = c[i]
    v1 = float((x - Pp) @ (Pm - Pp))          # should be <= 0 (x on inner side of chord Pm-Pp)
    v2 = float((x - Pm) @ (Pp - Pm))
    worst = max(worst, v1, v2)
    print(' ring%d: (x-Pi).(P_{i-1}-Pi)=%+.6f  (x-P_{i-1}).(Pi-P_{i-1})=%+.6f  |x-Pi|=%.6f |x-P_{i-1}|=%.6f'
          % (i, v1, v2, np.linalg.norm(x-Pp), np.linalg.norm(x-Pm)))
print('worst containment slack (must be <=0):', worst)

# closure residual, both conventions
print()
print('closure residuals (T,L as interior angles at P of the two fan triangles;',
      'apex = unsigned angle between the two ring sites at P):')
print('  i   resid_unsigned   resid_signed_TL   w_i/2 check  T+L vs w_i/2')
tot = 0
for k in range(9):
    i, j = k, (k+1) % 9
    P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
    T = angabs(Pm - P, c[i] - P)
    L = angabs(Pp - P, c[j] - P)
    apex = angabs(c[i] - P, c[j] - P)
    th = [math.atan2(x[1], x[0]) % (2*math.pi) for x in S]
    order = sorted(range(9), key=lambda q: th[q])
    ths = [th[q] for q in order]
    w = [(ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)]
    wl = w[order.index((k-1) % 9)]; wr = w[order.index(k)]
    r1 = T + L + apex + (wl+wr)/2 - math.pi
    print('  %d   %+.6e      %+.6e        T+L=%+.6f  (wl+wr)/2=%+.6f  diff=%+.3e'
          % (k, r1, 0.0, T+L, (wl+wr)/2, T+L-(wl+wr)/2))
