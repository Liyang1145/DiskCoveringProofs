# -*- coding: utf-8 -*-
"""
core_cover7.py -- EXACT two-hub core-disk covering criterion (final; verified).

SETUP.  D unit closed disk; 11 equal radius-r disks, r <= 19/50; 9 rings with
|c_i| >= 1-r (they touch bd D), 2 hubs h1,h2, |h_j| < 1-r.  a := 1-2r > 0.
For |x| < a:   |x - c_i| >= (1-r) - |x| > r,
so the core disk B(0,a) must be covered by the two hubs:
        B(0,a)  subset  B(h1,r) U B(h2,r).                                    (*)

EXACT CRITERION.
s_j=|h_j|, delta=angle(h1,h2), L=|h1-h2|>0, m_j=(h_j-h_k)/L, c_j=(s_j^2-s_k^2)/(2L).
C_j = {x : x.m_j >= c_j} is the Voronoi cell of h_j, so
       max_{B(0,a)} min_j |x-h_j| = max_j  max_{ C_j cap B(0,a) } |x-h_j| =: max_j M_j.
Writing x = a(cos t m_j + sin t m_j^perp),  C_j cap {|x|=a} = {cos t >= c_j/a}, and
   |x-h_j|^2 = a^2 + s_j^2 - 2a( ell_j cos t + beta_j sin t ),
   ell_j = h_j.m_j = (s_j^2 - s_k cos delta)/L,  beta_j = |h_j.m_j^perp| >= 0.
The maximum over t at fixed a of the linear form is at t=0 (value ell_j) if
t=0 is allowed, i.e. c_j <= 0; otherwise it is at the arc end t with
cos t = c_j/a, where the two signs give
   M_j^2 = a^2 + s_j^2 - 2c_j ell_j -+ 2 sqrt(a^2-c_j^2) beta_j,
and only ONE sign survives (the other sign's arc lies outside the cell), giving
   M_j = sqrt( a^2 + s_j^2 - 2 c_j ell_j - 2 sqrt(a^2-c_j^2) beta_j ).
[The point x is in the cap iff |x| <= a and x.m_j >= c_j; we only evaluate points on
 |x| = a at the allowed arc ends, so this is exactly the max over the cap boundary.]
Full criterion:
   c_j <= -a :  the whole disk lies in C_j  ->  M_j = a + s_j
   -a < c_j <= a : M_j = sqrt(a^2+s_j^2-2c_j ell_j - 2 sqrt(a^2-c_j^2) beta_j)
   c_j > a   :  C_j misses B(0,a) entirely (contributes nothing)
and (*) <=> max_j M_j <= r.
Cases where a cell contributes nothing still leave the OTHER cell to cover the disk:
then that other cell must cover it, i.e. its M must be <= r (this encodes "one hub
alone covers the core").

Verified against a dense grid oracle (no optimizer) on random configurations.
"""
import numpy as np, sys

def M_exact(a, s1, s2, delta, j, L=None):
    s = (s1, s2)[j]; t = (s1, s2)[1-j]
    if L is None:
        L = np.hypot(s1 - s2*np.cos(delta), s2*np.sin(delta))
    if L <= 1e-300:
        return a + s, 'coincident'
    c = (s*s - t*t)/(2.0*L)
    ell = (s*s - t*np.cos(delta))/L
    beta = np.sqrt(max(s*s - ell*ell, 0.0))
    if c <= -a:
        return a + s, 'disk-in-cell'
    if c <= a:
        val = a*a + s*s - 2*c*ell - 2*np.sqrt(max(a*a - c*c, 0.0))*beta
        return np.sqrt(max(val, 0.0)), 'arc-end'
    return -np.inf, 'cell-misses-core'

def core_covered_exact(a, r, s1, s2, delta):
    L = np.hypot(s1 - s2*np.cos(delta), s2*np.sin(delta))
    m0, w0 = M_exact(a, s1, s2, delta, 0, L); m1, w1 = M_exact(a, s1, s2, delta, 1, L)
    return (max(m0, m1) <= r + 1e-13), max(m0, m1), (w0, w1)

def circle_criterion(a, r, s1, s2, delta):
    if s1 <= 0 or s2 <= 0: return True
    b1 = np.arccos(np.clip((a*a+s1*s1-r*r)/(2*a*s1), -1, 1))
    b2 = np.arccos(np.clip((a*a+s2*s2-r*r)/(2*a*s2), -1, 1))
    return b1 + b2 >= 2*np.pi - delta - 1e-13

def oracle(a, s1, s2, delta, ngrid=701, nang=7001):
    h1 = np.array([s1, 0.0]); h2 = np.array([s2*np.cos(delta), s2*np.sin(delta)])
    rs = np.linspace(0, a, ngrid); th = np.linspace(0, 2*np.pi, nang, endpoint=False)
    R, T = np.meshgrid(rs, th, indexing='ij')
    X = R*np.cos(T); Y = R*np.sin(T)
    M = np.minimum(np.hypot(X-h1[0], Y-h1[1]), np.hypot(X-h2[0], Y-h2[1]))
    k = np.unravel_index(np.argmax(M), M.shape)
    return M[k], np.array([X[k], Y[k]])

def run_verify(r, ntest, seed=1):
    a = 1.0-2*r; rng = np.random.default_rng(seed); worst = 0.0; bad = []
    for _ in range(ntest):
        s1 = rng.uniform(0, 1-r); s2 = rng.uniform(0, 1-r); delta = rng.uniform(0, np.pi)
        ok, me, pc = core_covered_exact(a, r, s1, s2, delta)
        mn, xm = oracle(a, s1, s2, delta, 351, 3501)
        diff = me - mn
        worst = max(worst, abs(diff))
        if diff < -4e-3 or diff > 8e-3:
            bad.append((float(s1), float(s2), float(delta), float(me), float(mn), float(diff), str(pc)))
    print(f"[verify] r={r} a={a:.6f} n={ntest}:  max|M_exact-oracle| = {worst:.3e}  outliers={len(bad)}")
    for b in bad[:10]:
        print("   OUTLIER s1=%.5f s2=%.5f d=%.5f exact=%.6f grid=%.6f diff=%.2e piece=%s" % b)
    return worst, bad

TESTS = [(0.2946,0.14,np.pi),(0.2946,0.2946,np.pi),(0.2946,0.2946,2.0),(0.29,0.29,np.pi),
         (0.14,0.14,np.pi),(0.26,0.26,np.pi),(0.24,0.14,np.pi),(0.20,0.30,np.pi),
         (0.10,0.60,np.pi),(0.14,0.62,np.pi),(0.05,0.50,np.pi),(0.0,0.30,np.pi),
         (0.2946,0.2946,1.5),(0.2614,0.2614,np.pi),(0.2614,0.2614,2.6),(0.10,0.10,np.pi),
         (0.05,0.05,np.pi),(0.14,0.30,np.pi),(0.14,0.40,np.pi),(0.13,0.55,np.pi),
         (0.12,0.60,np.pi),(0.20,0.20,np.pi),(0.25,0.25,np.pi),(0.2946,0.20,np.pi),
         (0.26,0.14,np.pi),(0.30,0.10,np.pi),(0.2946,0.05,np.pi)]

if __name__ == "__main__":
    r = float(sys.argv[2]) if len(sys.argv) > 2 else 0.38
    a = 1-2*r
    print("="*104); print(f"A. exact criterion vs dense-grid oracle  (r={r}, a={a:.6f})"); print("="*104)
    run_verify(r, int(sys.argv[1]) if len(sys.argv) > 1 else 300)
    print(); print("="*104); print("B. calibration configurations"); print("="*104)
    for (s1,s2,d) in TESTS:
        ok, me, pc = core_covered_exact(a,r,s1,s2,d)
        mn, xm = oracle(a,s1,s2,d,701,7001)
        print(f" s1={s1:.4f} s2={s2:.4f} d={d:.3f} | maxM={me:.5f} {pc} | EXACT={str(ok):5s} "
              f"(oracle m={mn:.5f} at {xm.round(4)}) | circ={str(circle_criterion(a,r,s1,s2,d)):5s} "
              f"| prod={str(s1*s2<=r*r-a*a+1e-13):5s}")
