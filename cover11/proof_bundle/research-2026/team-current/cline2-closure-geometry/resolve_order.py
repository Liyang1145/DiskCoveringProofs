"""Exact numeric resolution of the ray-order question (no hand arithmetic)."""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import ConvexHull
ROOT = Path(__file__).resolve().parents[3]

def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def dir_deg(u): return math.degrees(math.atan2(u[1], u[0])) % 360

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A[i, 1], A[i, 0]))
c = A[rings+hubs]

# switches (nearest-site bisector points on |x|=1)
S = {}
for k in range(9):
    i, j = k, (k+1) % 9
    m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
    n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
        if np.linalg.norm(x-c[i]) - min(np.linalg.norm(q-x) for q in c) > 1e-9: continue
        S[k] = x

hull = ConvexHull(np.array([S[k] for k in range(9)]))
Kv = np.array([S[k] for k in range(9)])
print('convex hull of the 9 switches: npoints=%d, vertices=%s' % (len(Kv), sorted(hull.vertices.tolist())))
# is each site in K?
def in_K(x, tol=1e-12):
    worst = -1e9
    cen = Kv.mean(axis=0)
    for (a, b) in hull.simplices:
        q1, q2 = Kv[a], Kv[b]
        n = np.array([-(q2-q1)[1], (q2-q1)[0]])
        if dot(cen-q1, n) < 0: n = -n
        worst = max(worst, dot(x-q1, n))
    return worst <= tol, worst
for k in range(9):
    ok, w = in_K(c[k])
    print('  site c%d in K? %s  outward slack %+.9f' % (k, ok, w))
for k in range(9, 11):
    ok, w = in_K(c[k])
    print('  hub  c%d in K? %s  outward slack %+.9f' % (k, ok, w))

print()
print('at each switch: angular positions (deg) of u=P_{k-1}-P, v=P_{k+1}-P, ci-P, cj-P')
for k in range(9):
    P = S[k]; u = S[(k-1) % 9]-P; v = S[(k+1) % 9]-P
    ci = c[k]-P; cj = c[(k+1) % 9]-P
    du, dv, dc = dir_deg(u), dir_deg(v), dir_deg(ci)
    dcj = dir_deg(cj)
    # signed angles from u
    def s(t): return (t-du) % 360
    print('  k=%d: u %7.3f  v %7.3f  ci %7.3f  cj %7.3f | signed from u: v %7.3f ci %7.3f cj %7.3f'
          % (k, du, dv, dc, dcj, s(dv), s(dc), s(dcj)))
    # exact signed angles via cross/dot
    print('        signed angle(u,v)=%+.6f  (u,ci)=%+.6f  (ci,cj)=%+.6f  (cj,v)=%+.6f   sum=%.6f'
          % (math.atan2(cross(u, v), dot(u, v)), math.atan2(cross(u, ci), dot(u, ci)),
             math.atan2(cross(ci, cj), dot(ci, cj)), math.atan2(cross(cj, v), dot(cj, v)),
             math.atan2(cross(u, v), dot(u, v))))
