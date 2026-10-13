"""Closure identity on a randomized family of genuine covers (including
nonconvex / unbalanced / near-degenerate ones), plus the containment test
'are all sites inside the convex hull of the 9 switches?'.

Exact family used (unconditionally a genuine cover at radius R):
  9 ring sites on a circle of radius rho, equally spaced, + 2 coincident hubs
  at the origin is NOT a cover; instead we use:
  hubs at the origin, ring sites placed so that the midpoints of every
  consecutive pair lie inside the hub disks.  Here we simply search over
  ring radius/angle profiles and select configurations whose exact covering
  radius (max over Voronoi vertices in D and over boundary switches) is <= R.
"""
import numpy as np, math, itertools, json
from pathlib import Path
from scipy.spatial import Delaunay, ConvexHull
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def circum(p):
    return np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))

def cover_radius(c):
    best = 0.0
    tri = Delaunay(c)
    for f in tri.simplices:
        v = circum(c[f]); r = np.linalg.norm(v-c[f[0]])
        if v @ v < 1.0: best = max(best, r)
    hull = ConvexHull(c)
    for (i, j) in hull.simplices:
        m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
        nrm = np.array([d[1], -d[0]])/np.linalg.norm(d)
        t0 = -(m @ nrm); s2 = 1 - m @ m
        if s2 < 0: continue
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*nrm
            if np.linalg.norm(x-c[i]) - min(np.linalg.norm(x-q) for q in c) < 1e-9:
                best = max(best, np.linalg.norm(x-c[i]))
    return best

def cell_crossings(points, i):
    n = len(points); cr = []
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

def switches(points):
    S = []
    for k in range(9):
        cr = cell_crossings(points, k)
        cand = []
        for x in cr:
            d = np.array([np.linalg.norm(x-q) for q in points])
            lst = list(np.argsort(d))
            if set(lst[:2]) == {k, (k+1) % 9}: cand.append(x)
        if len(cand) != 1: return None
        S.append(cand[0])
    return S

def closure_res(points, S):
    c = points
    th = [math.atan2(x[1], x[0]) % (2*math.pi) for x in S]
    order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
    w = [(ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)]
    res = []
    for k in range(9):
        i, j = k, (k+1) % 9
        P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
        def ang(u, v): return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))
        T = ang(Pm-P, c[i]-P); L = ang(c[j]-P, Pp-P); apex = ang(c[i]-P, c[j]-P)
        wl = w[order.index((k-1) % 9)]; wr = w[order.index(k)]
        res.append(T+L+apex+(wl+wr)/2-math.pi)
    return res, w

def containment(points, S):
    """max over sites of min over the 8 chord half-planes (should be <= 0)."""
    pts = np.array([S[k] for k in sorted(range(9), key=lambda k: math.atan2(S[k][1], S[k][0]))])
    worst = -1e9
    for x in points:
        m = -1e9
        for k in range(9):
            P = pts[k]; Q = pts[(k+1) % 9]
            n = np.array([-(Q-P)[1], (Q-P)[0]])   # left normal of the CCW boundary
            if (Q-P)[0]*P[1]-(Q-P)[1]*P[0] < 0: n = -n   # point into the interior
            m = max(m, float((x-P) @ n))
        worst = max(worst, m)
    return worst

if __name__ == '__main__':
    rng = np.random.default_rng(7)
    ok = 0; tested = 0; bad = []
    for trial in range(4000):
        # random ring radius profile + random angular jitter, hubs random inside
        base = rng.uniform(0.70, 0.94, 9)
        ang = np.arange(9)*2*math.pi/9 + rng.uniform(-0.10, 0.10, 9)
        c = np.c_[base*np.cos(ang), base*np.sin(ang)]
        hub = rng.uniform(-0.30, 0.30, (2, 2))
        pts = np.vstack([c, hub])
        cr = cover_radius(pts)
        if cr > R: continue
        S = switches(pts)
        if S is None: continue
        tested += 1
        res, w = closure_res(pts, S)
        cont = containment(pts, S)
        m = max(abs(t) for t in res)
        if m > 1e-9:
            bad.append((trial, m, cont, cr))
            if len(bad) <= 5:
                print('CLOSURE FAIL trial', trial, 'max|res|=%.3e' % m, 'containment=%.4f' % cont, 'coverR=%.6f' % cr)
        # also report containment statistics
        if tested <= 5: print('   cover %d: max|res|=%.2e containment=%.4f widths=%s' % (tested, m, cont, np.round(w, 5)))
        ok += 1
        if tested >= 400: break
    print('genuine covers tested:', tested, ' closure failures:', len(bad))
    if bad: print('worst:', max(bad, key=lambda t: t[1]))
