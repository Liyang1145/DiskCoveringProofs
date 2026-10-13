# -*- coding: utf-8 -*-
"""
core_cover_geometry3.py -- exact two-hub core-disk covering criterion.

SETUP.  D unit closed disk; 11 equal radius-r disks, r <= 19/50; 9 rings touch bd(D)
(|c_i| >= 1-r), 2 hubs h1,h2 with |h_j| < 1-r.  For |x| < a := 1-2r:
    |x - c_i| >= (1-r) - |x| > r,
so B(0,a) can only be covered by the two hubs:
    B(0,a)  subset  B(h1,r) U B(h2,r).                                    (*)

EXACT CRITERION (this file: derive + verify + calibrate).
Let s_j = |h_j|, delta = angle(h1,h2), L = |h1-h2| > 0, C_j = Voronoi cell of h_j.
    B(0,a) covered  <=>  max_{B(0,a)} min_j |x-h_j| <= r
                    <=>  max_j  max_{B(0,a) cap C_j} |x-h_j| <= r.
On B(0,a) cap C_j the boundary splits into
  (i) the circular arc {|x| = a} cap C_j  -- largest value over the WHOLE circle is a+s_j,
      attained at x = a*hhat_j, which is always in C_j (norm identity
      |a*h_j/|h_j| - h_j| = |a-s_j| <= |a*h_j/|h_j| - h_k|   ).  [so this is a bound]
  (ii) the chord L_j = {x : |x-h_j| = |x-h_k|} cap B(0,a)  (if the bisector line cuts).
       Parametrise:  m = (h_k - h_j), mhat = m/|m|, n_j = (a^2+s_j^2-s_k^2)/2,
       x = (n_j/|m|) mhat + tau * mhat_perp,  |tau| <= sqrt(a^2 - (n_j/|m|)^2).
       Then |x - h_j|^2 = |c mhat - h_j|^2 + tau^2  with c = n_j/|m|; the maximum is at the
       endpoints,  |c mhat - h_j| = |c - ell_j| where ell_1 = (s1^2-s2^2)/L, ell_2 = -ell_1.
       => value  |c - ell_j| + sqrt(a^2 - c^2)   (endpoint with the + sign).
  (iii) chord cap halfplane C_j restriction: the two endpoints above both satisfy
       |x-h_j| <= |x-h_k| (equality on the chord), and the entire chord lies in the
       closure of both cells, so nothing is lost.
=> M_j = max( a + s_j , I_j ),  I_j = |c - ell_j| + sqrt(a^2 - c^2) if |c| <= a else -inf,
   and  (*) holds  <=>  max(M_1, M_2) <= r.

Cross-checks stored: (1) dense grid + SLSQP polish of min_j|x-h_j| over B(0,a);
(2) the "circle condition" b_1+b_2 >= 2pi - delta (necessary: it covers bd B(0,a));
(3) the product condition s1*s2 <= r^2-a^2 (necessary, weaker).
"""
import numpy as np
from scipy.optimize import minimize
import sys, json

def M_exact(a, s1, s2, delta, j):
    s = (s1, s2)[j]; t = (s1, s2)[1-j]
    L = np.hypot(s1 - s2*np.cos(delta), s2*np.sin(delta))
    val = a + s               # piece (i)
    piece = 'circle'
    if L > 1e-300:
        n = (a*a + s*s - t*t)/2.0
        ell = (s1*s1 - s2*s2)/L * (1.0 if j == 0 else -1.0)
        c = n/L
        if c*c <= a*a:
            v = abs(c - ell) + np.sqrt(max(a*a - c*c, 0.0))
            if v > val:
                val = v; piece = 'bisector'
    return val, piece

def core_covered_exact(a, r, s1, s2, delta):
    M0, p0 = M_exact(a, s1, s2, delta, 0); M1, p1 = M_exact(a, s1, s2, delta, 1)
    return (max(M0, M1) <= r + 1e-13), max(M0, M1), (p0, p1)

def circle_criterion(a, r, s1, s2, delta):
    if s1 <= 0 or s2 <= 0:
        return True
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
    for st in (x0, np.zeros(2), a*np.array([np.cos(0.7), np.sin(0.7)]),
               a*np.array([np.cos(2.4), np.sin(2.4)])):
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
        mn, xm = core_gap_numeric(a, s1, s2, delta, 141, 841)
        err = abs(me-mn); worst = max(worst, err)
        if err > 3e-3:
            bad.append((float(s1), float(s2), float(delta), float(me), float(mn), float(err), str(pc)))
    print(f"[verify] r={r} a={a:.6f} n={ntest}  max|M_exact-numeric|={worst:.3e}  mismatches={len(bad)}")
    for b in bad[:6]:
        print("   MISMATCH s1=%.5f s2=%.5f d=%.5f exact=%.6f num=%.6f err=%.2e piece=%s" % b)
    return worst, bad

if __name__ == "__main__":
    r = float(sys.argv[2]) if len(sys.argv) > 2 else 0.38
    a = 1-2*r
    print("="*104)
    print(f"A. exact criterion vs numeric truth  (r={r}, a={a:.6f})")
    print("="*104)
    run_verify(r, int(sys.argv[1]) if len(sys.argv) > 1 else 400)
    print()
    print("="*104)
    print("B. candidate criteria at calibration configurations")
    print("="*104)
    tests = [(0.2946,0.14,np.pi),(0.2946,0.2946,np.pi),(0.2946,0.2946,2.0),(0.29,0.29,np.pi),
             (0.29,0.29,2.3),(0.14,0.14,np.pi),(0.26,0.26,np.pi),(0.24,0.14,np.pi),
             (0.20,0.30,np.pi),(0.10,0.60,np.pi),(0.14,0.62,np.pi),(0.05,0.50,np.pi),
             (0.00,0.30,np.pi),(0.2946,0.2946,1.5),(0.2946,0.2946,1.0),(0.2614,0.2614,np.pi),
             (0.2614,0.2614,2.6),(0.2614,0.2614,2.9)]
    for (s1,s2,d) in tests:
        ok, me, pc = core_covered_exact(a,r,s1,s2,d)
        mn, xm = core_gap_numeric(a,s1,s2,d,161,961)
        print(f" s1={s1:.4f} s2={s2:.4f} d={d:.3f} | maxM={me:.5f} piece={pc} | EXACT={str(ok):5s} "
              f"(num={mn:.5f} at {xm.round(4)}) | circ={str(circle_criterion(a,r,s1,s2,d)):5s} "
              f"| prod={str(s1*s2<=r*r-a*a+1e-13):5s}")
