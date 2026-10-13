"""Genuine-cover generator with hub optimization (Nelder-Mead), then closure audit."""
import numpy as np, math, json, sys
from pathlib import Path
from scipy.spatial import Delaunay, ConvexHull
from scipy.optimize import minimize
ROOT = Path(__file__).resolve().parents[3]
R = 0.38
sys.path.insert(0, str(Path(__file__).parent))
from cover_search2 import circum, cover_radius, switches, closure_res, containment

def find_cover(seed, tries=3):
    r = np.random.default_rng(seed)
    rad = r.uniform(0.84, 0.94, 9)
    ang = np.arange(9)*2*math.pi/9 + r.uniform(-0.06, 0.06, 9)
    ang = np.sort(ang)
    if np.min(np.diff(np.r_[ang, ang[0]+2*math.pi])) < 0.35: return None
    ring = np.c_[rad*np.cos(ang), rad*np.sin(ang)]
    def f(h):
        pts = np.vstack([ring, h[:2], h[2:]])
        return cover_radius(pts)
    best = None
    for t in range(tries):
        h0 = r.uniform(-0.30, 0.30, 4)
        res = minimize(f, h0, method='Nelder-Mead',
                       options=dict(maxiter=400, maxfev=800, xatol=1e-9, fatol=1e-11))
        if best is None or res.fun < best.fun: best = res
    if best.fun <= R:
        pts = np.vstack([ring, best.x[:2], best.x[2:]])
        return pts, best.fun
    return None, None

if __name__ == '__main__':
    tested = 0; fails = 0; cont = []; mins = []
    for seed in range(300):
        pts, cr = find_cover(seed)
        if pts is None: continue
        S = switches(pts)
        if S is None: continue
        res, w, th = closure_res(pts, S)
        m = max(abs(t) for t in res); ct = containment(pts, S)
        tested += 1; cont.append(ct); mins.append(min(w))
        if m > 1e-9:
            fails += 1
            if fails <= 8:
                print('CLOSURE FAIL seed %d cr=%.7f max|res|=%.3e cont=%.4f' % (seed, cr, m, ct))
        if tested <= 3:
            print('cover seed %d: cr=%.8f max|res|=%.2e containment=%.4f minwidth=%.6f'
                  % (seed, cr, m, ct, min(w)))
        if tested >= 80: break
    print('genuine covers tested:', tested, 'closure failures:', fails)
    if cont:
        print('containment: min %.4f max %.4f (positive=site outside switch polygon in %d/%d)'
              % (min(cont), max(cont), sum(1 for t in cont if t > 1e-9), len(cont)))
        print('min width over covers: %.6f   (w >= 2pi-16asinR = %.6f)'
              % (min(mins), 2*math.pi-16*math.asin(R)))
