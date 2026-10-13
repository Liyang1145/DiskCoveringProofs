# -*- coding: utf-8 -*-
"""
core_cover4.py -- exact two-hub core-disk covering criterion (FINAL form).

SETUP.  D unit closed disk; 11 equal radius-r disks, r <= 19/50; 9 rings touch bd(D)
(|c_i| >= 1-r), 2 hubs h1,h2 with |h_j| < 1-r.  For |x| < a := 1-2r:
      |x - c_i| >= (1-r) - |x| > r,
so B(0,a) can only be covered by the hubs:   B(0,a) subset B(h1,r) U B(h2,r).   (*)

EXACT CRITERION.
s_j = |h_j|, delta = angle(h1,h2), L = |h1-h2| > 0, C_j = Voronoi cell of h_j,
   max_{B(0,a)} min_j |x-h_j| = max_j  max_{ B(0,a) cap C_j } |x-h_j|.
On B(0,a) cap C_j the boundary is
  (i)  the circular arc {|x|=a} cap C_j.  Over the whole circle the max is a+s_j at
       x = a*hhat_j, and x in C_j (norm identity).  Also the other arc end is a vertex.
  (ii) the bisector chord.  Put v = h_k - h_j, mhat = v/L; the bisector is
       n_j := (a^2+s_j^2-s_k^2)/2 = x . v, i.e.  x . mhat = n_j/L =: c_j.
       The chord is nonempty iff |c_j| <= a, and then its endpoints are
            e_pm = c_j*mhat +- sqrt(a^2-c_j^2) * mhat_perp.
       These are exactly the vertices of B(0,a) cap C_j.
  (iii) no other boundary.
So the maximum over B(0,a) cap C_j is attained at {a*hhat_j} U {e_+, e_-}, and
       |e_pm - h_j| = sqrt( (a - c_j)^2 + (a^2 - c_j^2) )
      => M_j = max( a + s_j ,  ([a - c_j]_+ + sqrt(a^2-c_j^2)) if |c_j|<=a ).
   (*) holds  <=>  max(M_1, M_2) <= r.

Verified against dense grid + SLSQP polish (below), on random configurations.
Controls: the "circle condition" b1+b2 >= 2pi-delta, and the "product condition"
s1*s2 <= r^2-a^2 (both necessary, the criterion is strictly stronger).
"""
import numpy as np
from scipy.optimize import minimize
import sys

def M_exact(a, s1, s2, delta, j):
    s = (s1, s2)[j]; t = (s1, s2)[1-j]
    L = np.hypot(s1 - s2*np.cos(delta), s2*np.sin(delta))
    val = a + s                                     # piece (i): x = a*hhat_j
    where = 'circle'
    if L > 1e-300:
        c = (a*a + s*s - t*t)/(2.0*L)
        if abs(c) <= a:                             # bisector cuts B(0,a)
            v = max(a - c, 0.0) + np.sqrt(max(a*a - c*c, 0.0))
            if v > val: val = v; where = 'bisector'
    return val, where

def core_covered_exact(a, r, s1, s2, delta):
    m0, w0 = M_exact(a, s1, s2, delta, 0); m1, w1 = M_exact(a, s1, s2, delta, 1)
    return (max(m0, m1) <= r + 1e-13), max(m0, m1), (w0, w1)

def circle_criterion(a, r, s1, s2, delta):
    if s1 <= 0 or s2 <= 0: return True
    b1 = np.arccos(np.clip((a*a+s1*s1-r*r)/(2*a*s1), -1, 1))
    b2 = np.arccos(np.clip((a*a+s2*s2-r*r)/(2*a*s2), -1, 1))
    return b1 + b2 >= 2*np.pi - delta - 1e-13

def core_gap_numeric(a, s1, s2, delta, ngrid=201, nang=1201):
    h1 = np.array([s1, 0.0]); h2 = np.array([s2*np.cos(delta), s2*np.sin(delta)])
    rs = np.linspace(0, a, ngrid); th = np.linspace(0, 2*np.pi, nang, endpoint=False)
    R, T = np.meshgrid(rs, th, indexing='ij')
    X = R*np.cos(T); Y = R*np.sin(T)
    M = np.minimum(np.hypot(X-h1[0], Y-h1[1]), np.hypot(X-h2[0], Y-h2[1]))
    k = np.unravel_index(np.argmax(M), M.shape); x0 = np.array([X[k], Y[k]]); best = M[k]
    def negm(x): return -min(np.hypot(*(x-h1)), np.hypot(*(x-h2)))
    for st in (x0, np.zeros(2), a*np.array([np.cos(.7), np.sin(.7)]),
               a*np.array([np.cos(2.4), np.sin(2.4)]), a*np.array([np.cos(4.1), np.sin(4.1)])):
        try:
            res = minimize(negm, st, method='SLSQP',
                           constraints=[{'type':'ineq','fun':lambda x: a*a-x[0]**2-x[1]**2}],
                           options={'ftol':1e-15,'maxiter':500})
            if -res.fun > best: best = -res.fun; x0 = res.x
        except Exception: pass
    return best, x0

def run_verify(r, ntest, seed=1):
    a = 1.0-2*r; rng = np.random.default_rng(seed); worst = 0.0; bad = []
    for _ in range(ntest):
        s1 = rng.uniform(0, 1-r); s2 = rng.uniform(0, 1-r); delta = rng.uniform(0, np.pi)
        ok, me, pc = core_covered_exact(a, r, s1, s2, delta)
        mn, xm = core_gap_numeric(a, s1, s2, delta, 151, 901)
        err = abs(me-mn); worst = max(worst, err)
        if err > 3e-3:
            bad.append((float(s1), float(s2), float(delta), float(me), float(mn), float(err),
                        str(pc), str(xm.round(4))))
    print(f"[verify] r={r} a={a:.6f} n={ntest}  max|M_exact-numeric| = {worst:.3e}  mismatches={len(bad)}")
    for b in bad[:8]:
        print("   MISMATCH s1=%.5f s2=%.5f d=%.5f exact=%.6f num=%.6f err=%.2e piece=%s x=%s" % b)
    return worst, bad

if __name__ == "__main__":
    r = float(sys.argv[2]) if len(sys.argv) > 2 else 0.38
    a = 1-2*r
    print("="*104); print(f"A. exact criterion vs numeric truth (r={r}, a={a:.6f})"); print("="*104)
    run_verify(r, int(sys.argv[1]) if len(sys.argv) > 1 else 400)
    print(); print("="*104); print("B. calibration configurations"); print("="*104)
    tests = [(0.2946,0.14,np.pi),(0.2946,0.2946,np.pi),(0.2946,0.2946,2.0),(0.29,0.29,np.pi),
             (0.29,0.29,2.3),(0.14,0.14,np.pi),(0.26,0.26,np.pi),(0.24,0.14,np.pi),
             (0.20,0.30,np.pi),(0.10,0.60,np.pi),(0.14,0.62,np.pi),(0.05,0.50,np.pi),
             (0.0,0.30,np.pi),(0.2946,0.2946,1.5),(0.2946,0.2946,1.0),(0.2614,0.2614,np.pi),
             (0.2614,0.2614,2.6),(0.2614,0.2614,2.9),(0.10,0.10,np.pi),(0.05,0.05,np.pi)]
    for (s1,s2,d) in tests:
        ok, me, pc = core_covered_exact(a,r,s1,s2,d)
        mn, xm = core_gap_numeric(a,s1,s2,d,161,961)
        print(f" s1={s1:.4f} s2={s2:.4f} d={d:.3f} | maxM={me:.5f} {pc} | EXACT={str(ok):5s} "
              f"(num={mn:.5f} at {xm.round(4)}) | circ={str(circle_criterion(a,r,s1,s2,d)):5s} "
              f"| prod={str(s1*s2<=r*r-a*a+1e-13):5s}")
