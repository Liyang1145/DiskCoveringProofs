"""Closure identity, take 2 -- with the exact switch definition.

Switch for the pair (c_i, c_j):
  P must satisfy |P| = 1,  |P - c_i| = |P - c_j| = rho,  and P must be the
  point at maximum distance from the origin among the two bisector-circle
  intersections, subject to containing the other sites?  Empirically the correct
  point is the ONE ON THE SIDE OPPOSITE to the outward normal of the pair, i.e.
  the more originward of the two circle/bisector intersections.  We test the
  two candidates: bisector lambda = m + t n with n = perp(c_j - c_i)/|.|
  t chosen with |P|=1.  Candidate A: t = t+ (farther out), B: t = t- .
  A genuine switch must satisfy min_k |P - c_k| = |P-c_i| (it is a Voronoi vertex).
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Delaunay, ConvexHull

ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def ang(u, v):
    c = float(u @ v)/np.linalg.norm(u)/np.linalg.norm(v)
    return math.acos(max(-1.0, min(1.0, c)))

def circum(p):
    return np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))

def cover_radius(points):
    best = 0.0
    tri = Delaunay(np.asarray(points))
    for f in tri.simplices:
        v = circum(points[f]); r = np.linalg.norm(v-points[f[0]])
        if v @ v < 1.0: best = max(best, r)
    hull = ConvexHull(np.asarray(points))
    for (i, j) in hull.simplices:
        m = 0.5*(points[i]+points[j]); d = points[j]-points[i]
        n = np.array([d[1], -d[0]])/np.linalg.norm(d)
        s2 = 1 - m @ m
        if s2 < 0: continue
        t0 = -(m @ n)
        for sgn in (+1, -1):
            x = m + (t0 + sgn*math.sqrt(t0*t0 + s2))*n
            if (np.linalg.norm(x-points[i]) - min(np.linalg.norm(x-q) for q in points)) < 1e-9:
                best = max(best, np.linalg.norm(x-points[i]))
    return best

def switch_pair(points, i, j, r):
    """The unique point P with |P|=1, |P-c_i|=|P-c_j|, that is nearest to all sites."""
    m = 0.5*(points[i]+points[j]); d = points[j]-points[i]
    n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    if s2 < 0: return None
    cands = [m + (t0 + sgn*math.sqrt(t0*t0 + s2))*n for sgn in (+1, -1)]
    best = None
    for x in cands:
        di = np.linalg.norm(x-points[i]); dj = np.linalg.norm(x-points[j])
        if abs(di-dj) > 1e-9: continue
        if di - min(np.linalg.norm(x-q) for q in points) > 1e-9: continue
        best = (x, di)
    return best

def analyse(name, points, r=R, verbose=True):
    points = np.asarray(points, float)
    info = {'name': name}
    cr = cover_radius(points)
    info['cover_radius'] = round(cr, 12); info['is_cover_at_r'] = bool(cr <= r + 1e-12)
    if not info['is_cover_at_r']:
        if verbose: print(json.dumps(info)); return info
    order = sorted(range(9), key=lambda i: math.atan2(points[i, 1], points[i, 0]))
    S = []
    for k in range(9):
        i, j = order[k], order[(k+1) % 9]
        got = switch_pair(points, i, j, r)
        if got is None:
            info['gap'] = f'no switch for pair ({i},{j})'; 
            if verbose: print(json.dumps(info)); return info
        S.append((i, j, got[0], got[1]))
    a = [math.atan2(t[2][1], t[2][0]) % (2*math.pi) for t in S]
    idx = sorted(range(9), key=lambda k: a[k])
    ang_sorted = [a[k] for k in idx]
    w = [(ang_sorted[(m+1) % 9] - ang_sorted[m]) % (2*math.pi) for m in range(9)]
    info['total_width'] = round(sum(w), 12); info['min_width'] = round(min(w), 9)
    info['widths'] = [round(t, 9) for t in w]
    info['closure'] = []
    for k in range(9):
        i, j, x, rad = S[k]
        # previous switch (shares site i): the pair (i-1,i); next switch: (j, j+1)
        prev = next((t[2] for t in S if t[1] == i and t[0] != j), None)
        nxt = next((t[2] for t in S if t[0] == j and t[1] != i), None)
        T = ang(prev - x, points[i] - x)
        L = ang(points[j] - x, nxt - x)
        apex = ang(points[i] - x, points[j] - x)
        kprev = next(kk for kk in range(9) if S[kk][1] == i)
        knew = next(kk for kk in range(9) if S[kk][0] == j)
        wid = (w[[m for m in range(9) if idx[m] == kprev][0]] + w[[m for m in range(9) if idx[m] == knew][0]])/2
        info['closure'].append(round(T + L + apex + wid - math.pi, 11))
    info['closure_max_abs'] = max(abs(t) for t in info['closure'])
    info['switch_radii'] = [round(t[3], 12) for t in S]
    if verbose: print(json.dumps(info))
    return info

def load_saved():
    p = ROOT / 'n11' / 'upper' / 'certified_object.json'
    raw = json.loads(p.read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings + hubs]

if __name__ == '__main__':
    s = load_saved()
    print('saved candidate: max|ring|=', round(float(np.max(np.linalg.norm(s[:9], axis=1))), 12),
          ' max|hub|=', round(float(np.max(np.linalg.norm(s[9:], axis=1))), 12))
    analyse('saved', s)
