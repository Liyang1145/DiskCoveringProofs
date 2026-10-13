"""Correct switch selection: the switch between two consecutive ring sites is the
endpoint of their shared Voronoi EDGE (ray) that lies on |x| = 1.

For each pair (i,j) that are Voronoi neighbours, the shared edge is the
perpendicular bisector ray between the two Voronoi vertices; we take the
intersection of the bisector LINE with |x|=1 that satisfies:
  - |S - p_i| = |S - p_j| <= |S - p_k| for all k,
  - the ray from S inward (S -> -S direction) leaves the pair region,
i.e. exactly the "switch" of the boundary-arc partition.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Voronoi
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def load_saved():
    raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings+hubs]

def boundary_switch(points, i, j):
    """The point of |x|=1 on the bisector of (i,j) that is nearest to all sites."""
    m = 0.5*(points[i]+points[j]); d = points[j]-points[i]
    n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    if s2 < 0: return None
    out = []
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        di = np.linalg.norm(x-points[i]); dj = np.linalg.norm(x-points[j])
        if abs(di-dj) > 1e-9: continue
        if di - min(np.linalg.norm(x-q) for q in points) > 1e-9: continue
        out.append(x)
    return out[0] if len(out) == 1 else (None if not out else min(out, key=lambda x: np.linalg.norm(x))) if len(out) > 1 else None

def analyse(name, c):
    c = np.asarray(c, float)
    vor = Voronoi(c)
    print('===', name)
    # Voronoi neighbour pairs (share an edge)
    pairs = set()
    for (pp, vv) in zip(vor.ridge_points, vor.ridge_vertices):
        if len(vv) == 2 and min(vv) >= 0:
            pairs.add(tuple(sorted(pp)))
        elif -1 in vv:
            pairs.add(tuple(sorted(pp)))
    ringpairs = [(i, (i+1) % 9) for i in range(9)]
    # determine which ring pairs are actually Voronoi neighbours
    print('ring-pair Voronoi adjacency:', [(i, j, tuple(sorted((i, j))) in pairs) for i, j in ringpairs])
    # switches
    sw = {}
    for i, j in ringpairs:
        S = boundary_switch(c, i, j)
        if S is None:
            print('   NO switch for pair', i, j); continue
        sw[(i, j)] = S
        d = np.array([np.linalg.norm(S-q) for q in c])
        lst = list(np.argsort(d))
        print('   pair(%d,%d): S angle %8.4f radius %.9f  2nd-nearest sites %s'
              % (i, j, math.degrees(math.atan2(S[1], S[0])) % 360, np.linalg.norm(S-c[i]),
                 [(int(t), round(float(d[t]), 6)) for t in lst[:4]]))
    # does every ring site's 2-cell meet |x|=1 at all? test by sampling
    print('   boundary owner runs:')
    prev = None; start = None
    for t in range(720):
        th = t*math.pi/360
        x = np.array([math.cos(th), math.sin(th)])
        d = np.array([np.linalg.norm(x-q) for q in c])
        o = int(np.argmin(d))
        if o != prev:
            if prev is not None: print('      owner %2d from %7.2f to %7.2f deg' % (prev, math.degrees(start), math.degrees(th)))
            prev, start = o, th
    print('      owner %2d from %7.2f to %7.2f deg' % (prev, math.degrees(start), 360.0))

if __name__ == '__main__':
    analyse('saved candidate', load_saved())
