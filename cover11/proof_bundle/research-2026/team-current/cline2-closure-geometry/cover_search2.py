"""Fast genuine-cover generator + closure/containment tests on many configurations.

Trick: for a fixed 9-ring profile, the covering radius is achieved either at a
boundary switch (function of the ring only) or at an interior Voronoi vertex.
Two coincident hubs at the origin give the largest hub disk; we therefore use a
small family of hub placements (origin, jittered) and keep configurations whose
exact covering radius <= R.
"""
import numpy as np, math, json
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
        v = circum(c[f]); r = float(np.linalg.norm(v-c[f[0]]))
        if v @ v < 1.0: best = max(best, r)
    for (i, j) in ConvexHull(c).simplices:
        m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
        nrm = np.array([d[1], -d[0]])/np.linalg.norm(d)
        t0 = -(m @ nrm); s2 = 1 - m @ m
        if s2 < 0: continue
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*nrm
            if float(np.linalg.norm(x-c[i]) - min(np.linalg.norm(x-q) for q in c)) < 1e-9:
                best = max(best, float(np.linalg.norm(x-c[i])))
    return best

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
            di = float(np.linalg.norm(x-points[i])); dj = float(np.linalg.norm(x-points[j]))
            if abs(di-dj) > 1e-9: continue
            if di - min(float(np.linalg.norm(x-q)) for q in points) > 1e-9: continue
            if not any(float(np.linalg.norm(x-y)) < 1e-7 for y in cr): cr.append(x)
    return cr

def switches(points):
    rings = sorted(range(9), key=lambda i: math.atan2(points[i, 1], points[i, 0]))
    S = []
    for k in range(9):
        i, j = rings[k], rings[(k+1) % 9]
        cand = []
        for x in cell_crossings(points, i):
            d = np.array([float(np.linalg.norm(x-q)) for q in points])
            if set(list(np.argsort(d))[:2]) == {i, j}: cand.append(x)
        if len(cand) != 1: return None
        S.append((i, j, cand[0]))
    return S

def closure_res(points, S):
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
        res.append(T+L+apex+(w[order.index((k-1) % 9)]+w[order.index(k)])/2 - math.pi)
    return res, w, th

def containment(points, S):
    pts = np.array([x[2] for x in sorted(S, key=lambda t: math.atan2(t[2][1], t[2][0]))])
    cen = pts.mean(axis=0); worst = -1e9
    for x in points:
        m = -1e9
        for k in range(9):
            P = pts[k]; Q = pts[(k+1) % 9]
            n = np.array([-(Q-P)[1], (Q-P)[0]])
            if float((cen-P) @ n) < 0: n = -n
            m = max(m, float((x-P) @ n))
        worst = max(worst, m)
    return worst

def run(seed_max=300, hubmodes=('origin', 'jit')):
    rng = np.random.default_rng(99)
    tested = 0; fails = 0; cont = []
    for seed in range(seed_max):
        r = np.random.default_rng(seed)
        rad = r.uniform(0.84, 0.94, 9)
        ang = np.arange(9)*2*math.pi/9 + r.uniform(-0.06, 0.06, 9)
        ang = np.sort(ang)
        if np.min(np.diff(np.r_[ang, ang[0]+2*math.pi])) < 0.18: continue
        ring = np.c_[rad*np.cos(ang), rad*np.sin(ang)]
        hubopts = [np.zeros(2)]
        for _ in range(4): hubopts.append(r.uniform(-0.34, 0.34, 2))
        for h in hubopts:
            pts = np.vstack([ring, h, h])
            cr = cover_radius(pts)
            if cr > R: continue
            S = switches(pts)
            if S is None: continue
            res, w, th = closure_res(pts, S)
            m = max(abs(t) for t in res)
            ct = containment(pts, S)
            tested += 1; cont.append(ct)
            if m > 1e-9:
                fails += 1
                if fails <= 8:
                    print('CLOSURE FAIL seed %d cr=%.7f max|res|=%.3e cont=%.4f widths=%s'
                          % (seed, cr, m, ct, np.round(w, 5)))
                    print('    res', ['%+.2e' % t for t in res])
            if tested >= 150: break
        if tested >= 150: break
    print('tested %d genuine covers; closure failures %d' % (tested, fails))
    if cont:
        print('containment slack: min %.4f max %.4f; positive (site outside switch polygon) in %d/%d'
              % (min(cont), max(cont), sum(1 for t in cont if t > 1e-9), len(cont)))
    return tested, fails

if __name__ == '__main__':
    run()
