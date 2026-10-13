"""Search for genuine covers at r=R=.38 by random ring profiles + hub optimization,
then test:
  (a) the closure identity  T_i + L_(i+1) + 2 b_i + (w_i+w_(i+1))/2 = pi
  (b) containment: are all sites inside the convex hull of the 9 switches?
  (c) degenerate cases: coincident switches, near-collinear/cocircular sites.
"""
import numpy as np, math, json, itertools
from pathlib import Path
from scipy.spatial import Delaunay, ConvexHull
from scipy.optimize import minimize
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def circum(p):
    return np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))

def cover_radius(c, want_points=False):
    best = 0.0; wv = None
    tri = Delaunay(c)
    for f in tri.simplices:
        v = circum(c[f]); r = np.linalg.norm(v-c[f[0]])
        if v @ v < 1.0 and r > best: best, wv = r, v
    hull = ConvexHull(c)
    for (i, j) in hull.simplices:
        m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
        nrm = np.array([d[1], -d[0]])/np.linalg.norm(d)
        t0 = -(m @ nrm); s2 = 1 - m @ m
        if s2 < 0: continue
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*nrm
            if np.linalg.norm(x-c[i]) - min(np.linalg.norm(x-q) for q in c) < 1e-9:
                r = np.linalg.norm(x-c[i])
                if r > best: best, wv = r, x
    return (best, wv) if want_points else best

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
    """the switch between consecutive ring sites (ordered by angle)."""
    rings = sorted(range(9), key=lambda i: math.atan2(points[i, 1], points[i, 0]))
    S = []
    for k in range(9):
        i, j = rings[k], rings[(k+1) % 9]
        cr = cell_crossings(points, i)
        cand = []
        for x in cr:
            d = np.array([np.linalg.norm(x-q) for q in points])
            lst = list(np.argsort(d))
            if set(lst[:2]) == {i, j}: cand.append(x)
        if len(cand) != 1: return None
        S.append((i, j, cand[0]))
    return S

def closure_info(points, S):
    th = [math.atan2(x[2][1], x[2][0]) % (2*math.pi) for x in S]
    order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
    w = [(ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)]
    res = []
    for k in range(9):
        i, j, P = S[k]
        Pm = S[(k-1) % 9][2]; Pp = S[(k+1) % 9][2]
        def ang(u, v): return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))
        T = ang(Pm-P, points[i]-P); L = ang(points[j]-P, Pp-P)
        apex = ang(points[i]-P, points[j]-P)
        wl = w[order.index((k-1) % 9)]; wr = w[order.index(k)]
        res.append(T+L+apex+(wl+wr)/2-math.pi)
    return res, w

def containment(points, S):
    pts = np.array([x[2] for x in sorted(S, key=lambda t: math.atan2(t[2][1], t[2][0]))])
    cen = pts.mean(axis=0)
    worst = -1e9
    for x in points:
        m = -1e9
        for k in range(9):
            P = pts[k]; Q = pts[(k+1) % 9]
            n = np.array([-(Q-P)[1], (Q-P)[0]])
            if float((cen-P) @ n) < 0: n = -n
            m = max(m, float((x-P) @ n))
        worst = max(worst, m)
    return worst

def make_cover(seed, mode='rand'):
    rng = np.random.default_rng(seed)
    for _ in range(40):
        if mode == 'rand':
            rad = rng.uniform(0.62, 0.95, 9)
            ang = np.arange(9)*2*math.pi/9 + rng.uniform(-0.35, 0.35, 9)
            if np.min(np.diff(np.r_[np.sort(ang), np.sort(ang)[0]+2*math.pi])) < 0.15: continue
            c = np.c_[rad*np.cos(ang), rad*np.sin(ang)]
        else:
            break
        # optimize 2 hubs by minimizing the covering radius
        def f(h):
            pts = np.vstack([c, h.reshape(2, 2)])
            return cover_radius(pts)
        best = None
        for _ in range(4):
            h0 = rng.uniform(-0.35, 0.35, 4)
            res = minimize(f, h0, method='Nelder-Mead', options=dict(maxiter=600, xatol=1e-10, fatol=1e-12))
            if best is None or res.fun < best.fun: best = res
        if best.fun <= R:
            return np.vstack([c, best.x.reshape(2, 2)]), best.fun
    return None, None

if __name__ == '__main__':
    found = 0; fails = 0; cont_stats = []; tested = 0
    for seed in range(400):
        pts, cr = make_cover(seed)
        if pts is None: continue
        S = switches(pts)
        if S is None: continue
        tested += 1
        res, w = closure_info(pts, S)
        m = max(abs(t) for t in res)
        ct = containment(pts, S)
        cont_stats.append(ct)
        if m > 1e-9:
            fails += 1
            if fails <= 6:
                print('CLOSURE FAIL seed %d max|res|=%.3e coverR=%.6f containment=%.4f' % (seed, m, cr, ct))
                print('   resid', ['%+.3e' % t for t in res])
        if tested <= 4:
            print('ok cover seed %d coverR=%.8f max|res|=%.2e containment=%.4f min width %.6f'
                  % (seed, cr, m, ct, min(w)))
        if tested >= 120: break
    print()
    print('genuine covers tested:', tested, ' closure failures:', fails)
    if cont_stats:
        print('containment: min %.4f  max %.4f  (#positive = sites outside switch polygon: %d/%d)'
              % (min(cont_stats), max(cont_stats), sum(1 for t in cont_stats if t > 1e-9), len(cont_stats)))
