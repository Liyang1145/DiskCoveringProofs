# -*- coding: utf-8 -*-
"""
core_cover_geometry.py -- EXACT core-disk covering criterion for two hubs.

Object: D = closed unit disk, 9 ring disks touching bd(D) + 2 hubs.
Rings have |c_i| >= 1-r  =>  for |x| < a := 1-2r,  |x-c_i| >= (1-r)-|x| > r.
Hence  B(0,a)  (a = 1-2r) must be covered by B(h1,r) U B(h2,r).

THIS FILE tests the exact criterion (Voronoi / nearest-point):
  core covered  <=>  max_{x in B(0,a)} min_j |x - h_j| <= r      [m(x) := min_j |x-h_j|]
  m is CONCAVE? No -- m = min of convex functions is NOT convex; but on the DISK the
  max of m can occur at an interior point (bisector).  We therefore use the exact
  decomposition:  core := (core cap C1) U (core cap C2),  C_j = Voronoi cell of h_j.
  On C_j cap B(0,a) the function |x-h_j| is convex and the set is convex, so the max is
  attained on its boundary = (bisector line) U (|x|=a).

Exact closed form tested here:
  A_j = a^2 + s_j^2 - r^2 - 2 a s_j
  P_j = (a^2 + s_j^2 - r^2) * (s_1^2 - s_2^2) + 2 s_j (r^2 - a^2)
  Q_j = 2 a sqrt(4 r^2 s_j^2 - (a^2 + s_j^2 - r^2)^2)
  M_j = max( A_j , max(0,P_j)+Q_j ) / (2 s_j)          [s_j > 0]
  core covered  <=>  M_j <= r for both j
(For s_j = 0, M_j = a.)

Control: high-resolution grid + scipy local maximisation of m over B(0,a).
"""
import numpy as np
from scipy.optimize import minimize
import sys

# ---------------- exact criterion ----------------
def M_exact(a, r, s1, s2, j):
    s = (s1, s2)[j]
    if s <= 0:
        return a
    A = a*a + s*s - r*r - 2*a*s
    rad = 4*r*r*s*s - (a*a + s*s - r*r)**2
    P = (a*a + s*s - r*r)*(s1*s1 - s2*s2) + 2*s*(r*r - a*a)
    Q = 2*a*np.sqrt(max(rad, 0.0))
    return max(A, (max(0.0, P) + Q))/(2*s)

def core_covered_exact(a, r, s1, s2, delta):
    """h1 = (s1,0), h2 = s2*(cos delta, sin delta)."""
    h1 = np.array([s1, 0.0]); h2 = np.array([s2*np.cos(delta), s2*np.sin(delta)])
    return M_exact(a, r, s1, s2, 0) <= r + 1e-15 and M_exact(a, r, s1, s2, 1) <= r + 1e-15

# ---------------- numeric truth ----------------
def m_of_x(x, h1, h2):
    return min(np.hypot(*(x-h1)), np.hypot(*(x-h2)))

def core_gap_numeric(a, r, s1, s2, delta, ngrid=241, nang=1441):
    """max of m over B(0,a) by dense grid + local polish; returns (max_m, argmax)."""
    h1 = np.array([s1, 0.0]); h2 = np.array([s2*np.cos(delta), s2*np.sin(delta)])
    rs = np.linspace(0.0, a, ngrid)
    th = np.linspace(0.0, 2*np.pi, nang, endpoint=False)
    R, T = np.meshgrid(rs, th, indexing='ij')
    X = R*np.cos(T); Y = R*np.sin(T)
    d1 = np.hypot(X-h1[0], Y-h1[1]); d2 = np.hypot(X-h2[0], Y-h2[1])
    M = np.minimum(d1, d2)
    k = np.unravel_index(np.argmax(M), M.shape)
    x0 = np.array([X[k], Y[k]]); best = M[k]
    # local polish maximising m over the disk (SLSQP with the |x|<=a constraint)
    def negm(x):
        return -m_of_x(x, h1, h2)
    for start in (x0, np.zeros(2)):
        res = minimize(negm, start, method='SLSQP',
                       constraints=[{'type':'ineq','fun':lambda x: a*a - x[0]**2 - x[1]**2}],
                       options={'ftol':1e-14, 'maxiter':400})
        if -res.fun > best:
            best = -res.fun; x0 = res.x
    return best, x0

# ---------------- runs ----------------
def run_verify(r=0.38, ntest=400, seed=1, verbose=True):
    a = 1.0 - 2*r
    rng = np.random.default_rng(seed)
    worst = 0.0; bad = []
    for _ in range(ntest):
        s1 = rng.uniform(0.0, 1.0-r); s2 = rng.uniform(0.0, 1.0-r)
        delta = rng.uniform(0.0, np.pi)
        me = max(M_exact(a, r, s1, s2, 0), M_exact(a, r, s1, s2, 1))
        mn, _ = core_gap_numeric(a, r, s1, s2, delta, ngrid=121, nang=721)
        err = abs(me - mn)
        worst = max(worst, err)
        if err > 3e-3:
            bad.append((s1, s2, delta, me, mn, err))
    if verbose:
        print(f"[verify] r={r} a={a:.6f} n={ntest} max|M_exact - numeric| = {worst:.3e}")
        for b in bad[:6]:
            print("   MISMATCH s1=%.6f s2=%.6f delta=%.6f exact=%.6f num=%.6f err=%.2e" % b)
    return worst, bad

def run_boundary_sweep(r=0.38, verbose=True):
    """find min over delta of feasible s2 for given s1 -- i.e. the domain boundary."""
    a = 1.0 - 2*r
    out = []
    for s1 in [0.0, 0.02, 0.05, 0.08, 0.10, 0.13, 0.14, 0.16, 0.18, 0.20, 0.22, 0.24,
               0.26, 0.28, 0.2946, 0.30, 0.35, 0.40, 0.45, 0.50, 0.55, 0.60]:
        s2s = np.linspace(0.0, 1.0-r, 4001)
        best = None
        for s2 in s2s:
            ok = False
            for delta in np.linspace(0.0, np.pi, 361):
                if core_covered_exact(a, r, s1, s2, delta):
                    ok = True; break
            # feasibility is monotone in s2? (no) -- scan whole list
            if ok:
                best = s2 if best is None else min(best, s2)
        # the product-only criterion for comparison
        prod = np.sqrt(max(r*r - a*a, 0.0))
        out.append((s1, best, prod))
        if verbose:
            pb = "inf" if best is None else "%.4f" % best
            print(f"   s1={s1:.4f}  min feasible s2 (exact disk) = {pb}   product-bound s1*s2<=r^2-a^2 would allow up to {prod/max(s1,1e-9):.4f}")
    return out

if __name__ == "__main__":
    r = 0.38; a = 1-2*r
    print("="*78)
    print("A. verification of the exact criterion vs numeric truth")
    print("="*78)
    run_verify(r=r, ntest=int(sys.argv[1]) if len(sys.argv) > 1 else 400)
    print()
    print("="*78)
    print("B. the two candidate (necessary) criteria, at the known witness (0.2946,0.14,pi)")
    print("="*78)
    for (s1, s2, d) in [(0.2946, 0.14, np.pi), (0.2946, 0.2946, np.pi), (0.29, 0.29, np.pi),
                        (0.2946, 0.2946, 2.0), (0.14, 0.14, np.pi), (0.26, 0.26, np.pi),
                        (0.27, 0.26, np.pi), (0.24, 0.14, np.pi), (0.20, 0.30, np.pi)]:
        b1 = np.arccos(np.clip((a*a+s1*s1-r*r)/(2*a*s1), -1, 1)) if s1 > 0 else np.pi
        b2 = np.arccos(np.clip((a*a+s2*s2-r*r)/(2*a*s2), -1, 1)) if s2 > 0 else np.pi
        circle_ok = (b1 + b2 >= 2*np.pi - d - 1e-12)
        prod_ok = (s1*s2 <= r*r - a*a + 1e-12)
        disk_ok = core_covered_exact(a, r, s1, s2, d)
        mn, xm = core_gap_numeric(a, r, s1, s2, d, ngrid=161, nang=961)
        print(f" s1={s1:.4f} s2={s2:.4f} d={d:.4f} | circle-crit={circle_ok}  product={prod_ok} "
              f"| EXACT-disk={disk_ok}  (numeric max m = {mn:.6f} vs r={r})  argmax={xm.round(5)}")
    print()
    print("="*78)
    print("C. domain boundary sweep")
    print("="*78)
    run_boundary_sweep(r=r)
