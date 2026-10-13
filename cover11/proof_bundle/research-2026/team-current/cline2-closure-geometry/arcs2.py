"""Exact boundary-ownership decomposition + closure identity, from coordinates only.

Robust cell-vertex enumeration (no Qhull interior-point issues):
vertices of cell(i) = points equidistant from site i and two others, inside cell(i).
Boundary crossings = cell edges intersected with |x|=1.
Then the 9 switches and the closure residual.
"""
import numpy as np, math, json, itertools
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def fitz(u, v):  # interior-exempt two-site bisector point not needed; use pairwise solver
    pass

def cell_vertices(points, i, tol=1e-9):
    """All Voronoi vertices of cell i (exact triple bisector intersections)."""
    n = len(points); out = []
    for j, k in itertools.combinations([t for t in range(n) if t != i], 2):
        # solve: |x-p_i|^2=|x-p_j|^2 and |x-p_i|^2=|x-p_k|^2
        A = np.array([2*(points[j]-points[i]), 2*(points[k]-points[i])])
        b = np.array([points[j]@points[j]-points[i]@points[i], points[k]@points[k]-points[i]@points[i]])
        if abs(np.linalg.det(A)) < 1e-12: continue
        x = np.linalg.solve(A, b)
        d = np.linalg.norm(x-points[i])
        if d >= min(np.linalg.norm(x-q) for q in points) - 1e-9:
            out.append(x)
    # dedupe
    res = []
    for x in out:
        if not any(np.linalg.norm(x-y) < 1e-7 for y in res): res.append(x)
    return res

def cell_crossings(points, i):
    """Crossings of cell(i)'s boundary with |x|=1."""
    n = len(points); cr = []
    # candidate rays: bisector of (i,j) intersected with |x|=1
    for j in range(n):
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

def load_saved():
    raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings+hubs]

def analyse(name, c):
    c = np.asarray(c, float)
    print('---', name)
    print('norms', np.round(np.linalg.norm(c, axis=1), 9))
    # switch between each consecutive ring pair
    S = []
    for k in range(9):
        cr = cell_crossings(c, k)
        # the switch to c_{k+1} is the crossing shared with site k+1
        cand = []
        for x in cr:
            d = np.array([np.linalg.norm(x-q) for q in c])
            lst = np.argsort(d + 1e-12*np.arange(len(d)))
            if set(lst[:2]) == {k, (k+1) % 9}: cand.append(x)
        if len(cand) != 1:
            print('  site %d: %d candidate switches' % (k, len(cand)))
            S.append(None); continue
        S.append(cand[0])
    if any(x is None for x in S): return
    th = [math.atan2(x[1], x[0]) % (2*math.pi) for x in S]
    order = sorted(range(9), key=lambda k: th[k])
    ths = [th[k] for k in order]
    w = [(ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)]
    print('  switch radii', np.round([np.linalg.norm(S[k]-c[k]) for k in range(9)], 12))
    print('  widths', np.round(w, 9), 'sum %.12f' % sum(w), 'min %.6f' % min(w))
    res = []
    for k in range(9):
        i, j = k, (k+1) % 9
        P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
        def ang(u, v):
            return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))
        T = ang(Pm-P, c[i]-P); L = ang(c[j]-P, Pp-P)
        apex = ang(c[i]-P, c[j]-P)
        wl = w[order.index((k-1) % 9)]; wr = w[order.index(k)]
        res.append(T+L+apex+(wl+wr)/2-math.pi)
    print('  closure residuals:', ['%+.2e' % t for t in res])
    print('  max |residual| = %.3e' % max(abs(t) for t in res))

if __name__ == '__main__':
    analyse('saved candidate', load_saved())
