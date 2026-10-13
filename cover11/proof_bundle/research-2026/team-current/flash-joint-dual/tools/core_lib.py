# -*- coding: utf-8 -*-
"""
core_lib.py -- calibrated core-coverage oracle for the two-hub reduction.

B(0,a), a = 1-2r, must be covered by B(h1,r) U B(h2,r)   (rings cannot reach it).
Define  m(x) = min_j |x - h_j|;  core covered  <=>  max_{|x|<=a} m(x) <= r.
Decomposition (exact):  max_{|x|<=a} m = max_j max_{C_j cap B(0,a)} |x-h_j|,
C_j = Voronoi cell of h_j = {x : x.m_j >= c_j},  m_j = (h_j-h_k)/L, c_j=(s_j^2-s_k^2)/(2L).
Both pieces are computed by fine 1-D scan + polish (Brent), which is calibrated against
a 2-D grid oracle.  Everything is a NECESSARY test for (*) -- we use it to map the
feasible hub domain, and cross-check against the analytic product criterion.
"""
import numpy as np
from scipy.optimize import minimize_scalar

def _maxj(a, s1, s2, delta, j, nt=20001, polish=True):
    s = (s1, s2)[j]; t = (s1, s2)[1-j]
    h = np.array([s, 0.0]) if j == 0 else np.array([s*np.cos(delta), s*np.sin(delta)])
    hk = np.array([t, 0.0]) if j == 1 else np.array([t*np.cos(delta), t*np.sin(delta)])
    v = h - hk; L = np.hypot(*v)
    if L <= 1e-300:
        return a + s
    mhat = v/L
    # C_j cap {|x|=a}:  a*cos t >= c  with x = a(cos t mhat + sin t mhat_perp)
    c = (s*s - t*t)/(2.0*L)
    if c <= -a * (1 - 1e-15):          # whole disk inside the cell
        return a + s
    if c > a * (1 + 1e-15):            # cell misses the disk
        return -np.inf
    ts = np.linspace(-np.pi/2, np.pi/2, nt)
    ok = np.cos(ts) >= (c/a) - 1e-15
    ts = ts[ok]
    if ts.size == 0:
        return -np.inf
    def dist2(t):
        x = a*(np.cos(t)*mhat + np.sin(t)*np.array([-mhat[1], mhat[0]]))
        return np.sum((x - h)**2)
    d2 = np.array([dist2(t) for t in ts[::max(1, ts.size//2000)]])
    k = int(np.argmax(d2))
    best = d2[k]
    if polish:
        t0 = ts[::max(1, ts.size//2000)][k]
        lo = max(t0 - 2*np.pi/2000, ts[0]); hi = min(t0 + 2*np.pi/2000, ts[-1])
        r = minimize_scalar(lambda t: -dist2(t), bounds=(lo, hi), method='bounded')
        best = max(best, -r.fun)
    return np.sqrt(max(best, 0.0))

def core_max_m(a, s1, s2, delta):
    """max_{|x|<=a} min_j |x-h_j| -- calibrated oracle."""
    return max(_maxj(a, s1, s2, delta, 0), _maxj(a, s1, s2, delta, 1))

def core_covered(a, r, s1, s2, delta, tol=1e-9):
    return core_max_m(a, s1, s2, delta) <= r + tol

def grid_oracle(a, s1, s2, delta, ngrid=701, nang=7001):
    h1 = np.array([s1, 0.0]); h2 = np.array([s2*np.cos(delta), s2*np.sin(delta)])
    rs = np.linspace(0, a, ngrid); th = np.linspace(0, 2*np.pi, nang, endpoint=False)
    R, T = np.meshgrid(rs, th, indexing='ij')
    X = R*np.cos(T); Y = R*np.sin(T)
    M = np.minimum(np.hypot(X-h1[0], Y-h1[1]), np.hypot(X-h2[0], Y-h2[1]))
    k = np.unravel_index(np.argmax(M), M.shape)
    return M[k], np.array([X[k], Y[k]])

def circle_ok(a, r, s1, s2, delta):
    if s1 <= 0 or s2 <= 0: return True
    b1 = np.arccos(np.clip((a*a+s1*s1-r*r)/(2*a*s1), -1, 1))
    b2 = np.arccos(np.clip((a*a+s2*s2-r*r)/(2*a*s2), -1, 1))
    return b1 + b2 >= 2*np.pi - delta - 1e-13

if __name__ == "__main__":
    import sys
    r = 0.38; a = 1-2*r
    print("="*100)
    print(f"CALIBRATION  r={r} a={a:.6f}:  analytic (scan+polish) vs 2-D grid oracle")
    print("="*100)
    rng = np.random.default_rng(7); worst = 0.0; nbad = 0
    for i in range(250):
        s1 = rng.uniform(0, 1-r); s2 = rng.uniform(0, 1-r); d = rng.uniform(0, np.pi)
        m1 = core_max_m(a, s1, s2, d); m2, xm = grid_oracle(a, s1, s2, d, 501, 5001)
        if m1 < m2 - 1e-6:                 # scan+polish must not undershoot the grid
            nbad += 1
            if nbad <= 5: print("   UNDERSHOOT s1=%.5f s2=%.5f d=%.5f scan=%.7f grid=%.7f" % (s1,s2,d,m1,m2))
        worst = max(worst, abs(m1 - m2))
    print(f"  max |scan+polish - grid| = {worst:.3e}   undershoots = {nbad}")
    print()
    print("="*100)
    print("KNOWN-ANSWER CONTROLS (analytic values)")
    print("="*100)
    ctrl = [ (0.2946,0.2946,np.pi, np.sqrt(a*a+0.2946**2), 'antipodal equal: max m = sqrt(a^2+s^2)'),
             (0.14,0.14,np.pi,    np.sqrt(a*a+0.14**2),   'antipodal small: sqrt(a^2+s^2)'),
             (0.0,0.30,np.pi,     a+0.30,                 'h1 at origin: a+s2'),
             (0.10,0.60,np.pi,    0.10+0.24,              's2 large: hub1 covers disk alone -> a+s1'),
             (0.2946,0.2946,0.0,  a+0.2946,               'coincident hubs: a+s') ]
    for (s1,s2,d,exp,name) in ctrl:
        got = core_max_m(a, s1, s2, d)
        print(f"  s1={s1:.4f} s2={s2:.4f} d={d:.3f}: got={got:.6f} expected={exp:.6f} "
              f"diff={got-exp:+.2e}   [{name}]")
    print()
    print("="*100)
    print("THE KEY QUESTION: is the product criterion s1*s2 <= r^2-a^2 the exact disk criterion?")
    print("="*100)
    print("  compute, for each s1, the minimal s2 such that some delta gives coverage:")
    for s1 in [0.0,0.05,0.10,0.14,0.20,0.24,0.2614,0.28,0.2946,0.30,0.35]:
        bests2 = None; bestd = None
        for s2 in np.arange(0.0, 1-r+1e-9, 0.001):
            for d in np.arange(0.0, np.pi+1e-9, 0.01):
                if core_covered(a, r, s1, s2, d):
                    if bests2 is None or s2 < bests2: bests2, bestd = s2, d
                    break
        prod_allowed = (r*r-a*a)/s1 if s1 > 1e-9 else np.inf
        print(f"   s1={s1:.4f}: min feasible s2 = {bests2} (at delta={bestd}) | "
              f"product bound allows s2 <= {prod_allowed:.4f} | s1*s2min = "
              f"{(s1*bests2 if bests2 is not None else float('nan')):.5f} vs r^2-a^2={r*r-a*a:.5f}")
