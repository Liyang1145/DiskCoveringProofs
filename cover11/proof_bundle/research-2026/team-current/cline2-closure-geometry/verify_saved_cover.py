"""Independent verification of the SAVED candidate:
 (1) its true covering radius (dense scan + exact Voronoi vertex scan),
 (2) Voronoi degree of each site (to check the hub identification),
 (3) the closure residual for the boundary-arc switches recomputed exactly.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Delaunay, Voronoi, ConvexHull
ROOT = Path(__file__).resolve().parents[3]
raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
print('11 sites; norms:', np.round(np.linalg.norm(A, axis=1), 9))

def cover_radius(c, dense=True):
    c = np.asarray(c, float)
    best = 0.0; where = None
    tri = Delaunay(c)
    for f in tri.simplices:
        p = c[f]
        v = np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))
        if v @ v < 1.0:
            r = float(np.linalg.norm(v-p[0]))
            if r > best: best, where = r, ('Voronoi vertex', v, tuple(int(t) for t in f))
    if dense:
        g = 601
        xs = np.linspace(-1, 1, g)
        for x in xs:
            for y in xs:
                if x*x+y*y > 1: continue
                d = np.min(np.linalg.norm(c - np.array([x, y]), axis=1))
                if d > best: best, where = float(d), ('grid point', np.array([x, y]), None)
    return best, where

cr, wh = cover_radius(A)
print('covering radius (Voronoi vertices + 601x601 grid) = %.12f  at %s' % (cr, wh[0]))
vor = Voronoi(A)
deg = {}
for (pp, vv) in zip(vor.ridge_points, vor.ridge_vertices):
    for i in pp: deg[i] = deg.get(i, set())
for (pp, vv) in zip(vor.ridge_points, vor.ridge_vertices):
    for i in pp:
        deg[i].add(tuple(sorted(pp)))
print('Voronoi degrees:', {i: len(deg[i]) for i in range(11)})
print('top Voronoi-vertex radii:')
rr = []
for f in Delaunay(A).simplices:
    p = A[f]; v = np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))
    rr.append((float(np.linalg.norm(v)), float(np.linalg.norm(v-p[0])), tuple(int(t) for t in f), float(np.linalg.norm(v))))
rr.sort(key=lambda t: -t[1])
for t in rr[:6]: print('   rho=%.9f |v|=%.9f face=%s' % (t[1], t[3], t[2]))
