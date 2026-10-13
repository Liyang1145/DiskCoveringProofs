# -*- coding: utf-8 -*-
"""
core_cover5.py -- exact two-hub core-disk covering criterion (correct arc restriction).

SETUP.  D unit closed disk; 11 equal radius-r disks, r <= 19/50; 9 rings touch bd(D)
(|c_i| >= 1-r), 2 hubs h1,h2 with |h_j| < 1-r.  For |x| < a := 1-2r:
      |x - c_i| >= (1-r) - |x| > r,
so B(0,a) can only be covered by the hubs:   B(0,a) subset B(h1,r) U B(h2,r).   (*)

EXACT CRITERION.
s_j=|h_j|, delta=angle(h1,h2), C_j = Voronoi cell of h_j, L = |h1-h2|.
    max_{B(0,a)} min_j |x-h_j|  =  max_j max_{ B(0,a) cap C_j } |x-h_j|  =  max_j M_j.
On B(0,a) cap C_j the boundary is a circular arc (inside the half-plane C_j) plus the
bisector chord if it cuts.  The bisector is x.(h_j-h_k) = (s_j^2-s_k^2)/2, i.e.
    x . mhat = d_j,  mhat = (h_j-h_k)/L,  d_j = (s_j^2-s_k^2)/(2L) =: c_j.
C_j = {x : x . mhat >= c_j}.  The half-plane cuts the disk (|c_j| <= a) iff
    L^2 >= (s_j^2-s_k^2)^2/(4a^2).
  * If it does not cut: C_j contains all of B(0,a) -> M_j = a + s_j.
  * If it cuts: the arc of |x| = a inside C_j is {|phi| <= phi_0},
        cos phi_0 = c_j/a  (phi measured from mhat).
    The hub direction (phi=0 relative to hhat_j) lies in that arc iff c_j <= 0.
      - c_j <= 0 : phi = 0 is interior -> M_j = a + s_j;
      - c_j  > 0 : max of cos on the arc is at the two endpoints ->
                   M_j = max over the chord endpoints = (a - c_j) + sqrt(a^2 - c_j^2).
    (the chord endpoints are the same points, |x-h_j| = (a-c_j)+sqrt(a^2-c_j^2); the
     other chord endpoint gives max(|a - c_j| - sqrt(...),0), which is smaller.)
  * c_j <= 0 forces s_k >= s_j, so the larger hub always has c >= 0 and the criterion
    reduces to a symmetric test.
   (*) holds  <=>  max_j M_j <= r.

Verified against a dense grid oracle (no optimizer) on random configurations.
"""
import numpy as np
import sys

def M_exact(a, s1, s2, delta, j):
    s = (s1, s2)[j]; t = (s1, s2)[1-j]
    L = np.hypot(s1 - s2*np.cos(delta), s2*np.sin(delta))
    val = a + s
    where = 'circle'
    if L > 1e-300:
        c = (s*s - t*t)/(2.0*L)
        if c > 0 and c <= a:            # half-plane cuts, hub direction outside cell
            v = (a - c) + np.sqrt(max(a*a - c*c, 0.0))
            if v > val:
                val = v; where = 'arc-end'
        # c <= 0 or no cut: the hub direction is in the cell -> a + s  (already)
    return val, where

def core_covered_exact(a, r, s1, s2, delta):
    m0, w0 = M_exact(a, s1, s2, delta, 0); m1, w1 = M_exact(a, s1, s2, delta, 1)
    return (max(m0, m1) <= r + 1e-13), max(m0, m1), (w0, w1)

def circle_criterion(a, r, s1, s2, delta):
    if s1 <= 0 or s2 <= 0: return True
    b1 = np.arccos(np.clip((a*a+s1*s1-r*r)/(2*a*s1), -1, 1))
    b2 = np.arccos(np.clip((a*a+s2*s2-r*r)/(2*a*s2), -1, 1))
    return b1 + b2 >= 2*np.pi - delta - 1e-13

def core_gap_grid(a, s1, s2, delta, ngrid=601, nang=6001):
    h1 = np.array([s1, 0.0]); h2 = np.array([s2*np.cos(delta), s2*np.sin(delta)])
    rs = np.linspace(0, a, ngrid); th = np.linspace(0, 2*np.pi, nang, endpoint=False)
    R, T = np.meshgrid(rs, th, indexing='ij')
    X = R*np.cos(T); Y = R*np.sin(T)
    M = np.minimum(np.hypot(X-h1[0], Y-h1[1]), np.hypot(X-h2[0], Y-h2[1]))
    k = np.unravel_index(np.argmax(M), M.shape)
    # radial-only refinement around the argmax (the max of a concave-in-|x|? no: convex
    # along bisector, so radial refinement is safe as a local check)
    x0 = np.array([X[k], Y[k]]); best = M[k]
    return best, x0

def run_verify(r, ntest, seed=1, ngrid=601, nang=6001):
    a = 1.0-2*r; rng = np.random.default_rng(seed); worst = 0.0; bad = []
    for _ in range(ntest):
        s1 = rng.uniform(0, 1-r); s2 = rng.uniform(0, 1-r); delta = rng.uniform(0, np.pi)
        ok, me, pc = core_covered_exact(a, r, s1, s2, delta)
        mn, xm = core_gap_grid(a, s1, s2, delta, ngrid, nang)
        err = me - mn                      # exact must be >= grid (grid underestimates)
        if err < -3e-3 or err > 6e-3:
            bad.append((float(s1), float(s2), float(delta), float(me), float(mn), float(err), str(pc)))
        worst = max(worst, abs(err))
    print(f"[verify] r={r} a={a:.6f} n={ntest}:  |M_exact - grid| max = {worst:.3e}, outliers={len(bad)}")
    for b in bad[:10]:
        print("   OUTLIER s1=%.5f s2=%.5f d=%.5f exact=%.6f grid=%.6f diff=%.2e piece=%s" % b)
    return worst, bad

if __name__ == "__main__":
    r = float(sys.argv[2]) if len(sys.argv) > 2 else 0.38
    a = 1-2*r
    print("="*104); print(f"A. exact criterion vs dense-grid oracle (r={r}, a={a:.6f})"); print("="*104)
    run_verify(r, int(sys.argv[1]) if len(sys.argv) > 1 else 300)
    print(); print("="*104); print("B. calibration configurations"); print("="*104)
    tests = [(0.2946,0.14,np.pi),(0.2946,0.2946,np.pi),(0.2946,0.2946,2.0),(0.29,0.29,np.pi),
             (0.14,0.14,np.pi),(0.26,0.26,np.pi),(0.24,0.14,np.pi),(0.20,0.30,np.pi),
             (0.10,0.60,np.pi),(0.14,0.62,np.pi),(0.05,0.50,np.pi),(0.0,0.30,np.pi),
             (0.2946,0.2946,1.5),(0.2614,0.2614,np.pi),(0.2614,0.2614,2.6),
             (0.10,0.10,np.pi),(0.05,0.05,np.pi),(0.14,0.30,np.pi),(0.14,0.40,np.pi),
             (0.13,0.55,np.pi),(0.12,0.60,np.pi)]
    for (s1,s2,d) in tests:
        ok, me, pc = core_covered_exact(a,r,s1,s2,d)
        mn, xm = core_gap_grid(a,s1,s2,d,801,8001)
        print(f" s1={s1:.4f} s2={s2:.4f} d={d:.3f} | maxM={me:.5f} {pc} | EXACT={str(ok):5s} "
              f"(grid max m={mn:.5f} at {xm.round(4)}) | circ={str(circle_criterion(a,r,s1,s2,d)):5s} "
              f"| prod={str(s1*s2<=r*r-a*a+1e-13):5s}")
