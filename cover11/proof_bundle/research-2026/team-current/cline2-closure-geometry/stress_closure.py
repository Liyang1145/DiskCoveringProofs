"""Independent stress test of the closure identity on non-symmetric 9-ring
configurations with hubs placed so that the covering radius is small.

We do NOT need an actual cover to test the identity: the identity is a statement
about the switch polygon, the ring sites and the owned arcs, and holds whenever
(i) each owned arc has both endpoints within r of its site (so the site is inside
K by Cauchy-Schwarz), and (ii) the switches are the nearest-site crossings.
We generate configurations, keep those satisfying the covering-radius condition
exactly (max over Voronoi vertices in D and boundary switches <= R), and test.
"""
import numpy as np, math
from scipy.spatial import Delaunay, ConvexHull
from scipy.optimize import minimize
R = 0.38

def circum(p):
    return np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))

def cover_radius(c):
    best = 0.0
    for f in Delaunay(c).simplices:
        p = c[f]; v = circum(p); r = float(np.linalg.norm(v-p[0]))
        if v @ v < 1.0: best = max(best, r)
    for (i, j) in ConvexHull(c).simplices:
        m = 0.5*(c[i]+c[j]); dd = c[j]-c[i]; n = np.array([dd[1], -dd[0]])/np.linalg.norm(dd)
        t0 = -(m @ n); s2 = 1 - m @ m
        if s2 < 0: continue
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
            if np.linalg.norm(x-c[i])-min(np.linalg.norm(q-x) for q in c) < 1e-9:
                best = max(best, float(np.linalg.norm(x-c[i])))
    return best

def switches(c):
    S = {}
    for k in range(9):
        i, j = k, (k+1) % 9
        m = 0.5*(c[i]+c[j]); dd = c[j]-c[i]; n = np.array([dd[1], -dd[0]])/np.linalg.norm(dd)
        t0 = -(m @ n); s2 = 1 - m @ m
        cand = []
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
            if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
            if np.linalg.norm(x-c[i])-min(np.linalg.norm(q-x) for q in c) > 1e-9: continue
            cand.append(x)
        if len(cand) != 1: return None
        S[k] = cand[0]
    return S

def closure(c, S):
    def ang(u, v):
        return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))
    th = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
    order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
    w = {order[m]: (ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)}
    res = []
    for i in range(9):
        P = S[i]
        tri = ang(S[(i-1) % 9]-P, c[i]-P) + ang(c[i]-P, c[(i+1) % 9]-P) + ang(c[(i+1) % 9]-P, S[(i+1) % 9]-P)
        theta = math.pi - (w[(i-1) % 9]+w[i])/2
        res.append(tri - theta)
    return res, w

def find(nseed=40, tries=4):
    out = []
    for seed in range(nseed):
        r = np.random.default_rng(seed)
        rad = r.uniform(0.84, 0.94, 9)
        ang0 = np.arange(9)*2*math.pi/9 + r.uniform(-0.08, 0.08, 9)
        ang0 = np.sort(ang0)
        if np.min(np.diff(np.r_[ang0, ang0[0]+2*math.pi])) < 0.30: continue
        ring = np.c_[rad*np.cos(ang0), rad*np.sin(ang0)]
        def f(h):
            return cover_radius(np.vstack([ring, h[:2], h[2:]]))
        best = None
        for t in range(tries):
            res = minimize(f, r.uniform(-0.3, 0.3, 4), method='Nelder-Mead',
                           options=dict(maxiter=350, maxfev=700, xatol=1e-9, fatol=1e-11))
            if best is None or res.fun < best.fun: best = res
        if best.fun <= R:
            c = np.vstack([ring, best.x[:2], best.x[2:]])
            S = switches(c)
            if S is None: continue
            res, w = closure(c, S)
            out.append((seed, best.fun, max(abs(t) for t in res), min(w)))
    return out

if __name__ == '__main__':
    got = find()
    print('genuine covers found:', len(got))
    for seed, cr, mx, mw in got[:12]:
        print('  seed %d coverR=%.9f max|closure resid|=%.2e min width=%.6f' % (seed, cr, mx, mw))
    if got:
        print('worst closure residual over all genuine covers: %.3e' % max(g[2] for g in got))
