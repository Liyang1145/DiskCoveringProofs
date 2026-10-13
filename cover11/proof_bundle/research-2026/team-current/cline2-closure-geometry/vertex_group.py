"""Correct vertex analysis with tolerance-based grouping of Voronoi vertices.

A Voronoi vertex of the diagram = a maximal equidistant set {i : |v-c_i|=rho_v}.
We reconstruct the vertices from the site data (exact circumcenters of
Delaunay triangles and of boundary triples) instead of trusting nearest-site
rankings, then measure the cell angles exactly.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Delaunay
ROOT = Path(__file__).resolve().parents[3]

def circum(*p):
    p = np.array(p)
    if len(p) == 3:
        return np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))
    return None

def vertex_list(c):
    """all Voronoi vertices of a 9-ring+2-hub configuration:
       circumcenters of Delaunay triangles + boundary switch points."""
    c = np.asarray(c, float)
    out = []
    for f in Delaunay(c).simplices:
        v = circum(c[f[0]], c[f[1]], c[f[2]])
        r = float(np.linalg.norm(v-c[f[0]]))
        out.append((v, r, tuple(int(t) for t in f), np.array([float(np.linalg.norm(v-q)) for q in c])))
    for k in range(9):
        for sgn in (-1, 1):
            i, j = k, (k+1) % 9
            m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
            n = np.array([d[1], -d[0]])/np.linalg.norm(d)
            t0 = -(m @ n); s2 = 1 - m @ m
            if s2 < 0: continue
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
            r = float(np.linalg.norm(x-c[i]))
            d2 = np.array([float(np.linalg.norm(x-q)) for q in c])
            out.append((x, r, (i, j), d2))
    return out

def analyse(c, tol=1e-6):
    c = np.asarray(c, float)
    V = vertex_list(c)
    good = [t for t in V if t[1] < 1.0]     # only vertices inside D matter
    print('vertices inside D:', len(good))
    # group by (position, radius) to merge duplicates
    uniq = []
    for v, r, f, d2 in good:
        hit = False
        for i, (v0, r0, fs, d0) in enumerate(uniq):
            if np.linalg.norm(v-v0) < 1e-7:
                fs2 = set(fs) | set(f)
                dd = np.minimum(d0, d2)
                uniq[i] = (v0, min(r0, r), tuple(sorted(fs2)), dd)
                hit = True; break
        if not hit: uniq.append((v, r, tuple(f), d2))
    print('distinct vertices inside D:', len(uniq))
    rows = []
    for (v, r, f, d2) in uniq:
        eq = [i for i in range(len(c)) if abs(d2[i]-d2[f[0]]) < tol]
        rows.append((v, r, f, eq, d2))
    rows.sort(key=lambda t: -t[1])
    for (v, r, f, eq, d2) in rows[:8]:
        print('  rho=%.9f |v|=%.9f face=%s equidistant=%s' % (r, np.linalg.norm(v), f, eq))
    return uniq

if __name__ == '__main__':
    raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
    A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    analyse(A)
