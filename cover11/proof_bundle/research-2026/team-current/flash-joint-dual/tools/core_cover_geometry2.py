# -*- coding: utf-8 -*-
"""
core_cover_geometry2.py -- CORRECTED exact core-disk covering criterion (two hubs).

Object: D = closed unit disk, 9 ring disks touching bd(D) + 2 hubs, r <= 19/50.
Rings: |c_i| >= 1-r  =>  for |x| < a := 1-2r, |x-c_i| > r.  So B(0,a) must be
covered by B(h1,r) U B(h2,r).

EXACT criterion (derived, then tested against numeric truth):
  m(x) := min_j |x-h_j|.   core covered  <=>  max_{x in B(0,a)} m(x) <= r.
  max_{B(0,a)} m = max_j  max_{ x in B(0,a) cap C_j } |x-h_j|      (C_j = Voronoi cell)
  On B(0,a) cap C_j:
    * boundary part on |x| = a  -> value a + s_j  (at x = a*hhat_j)
    * boundary part on the bisector line, IF the line cuts the disk:
        n_j := (a^2 + s_j^2 - s_k^2)/2,  c_j := n_j/|h_k - h_j|,
        cuts iff n_j^2 < a^2 |h_k-h_j|^2;  then the value there is
        I_j = c_j + sqrt(a^2 - n_j^2/|h_k-h_j|^2)
      (the other endpoint is the minimum of |x-h_j| on the whole line
       restricted to the disk, value max(0, c_j - sqrt(...)) )
    * if the line does not cut -> no bisector contribution.
  => M_j = max(a + s_j, I_j)  (I_j = 0 if no cut);  core covered <=> max_j M_j <= r.

Equivalent INTERSECTION form (provable directly, one line):
  core covered  =>  for each j the point at distance exactly r outside B(h_j,r) along
  hhat_j lies in B(0,a):  (a^2 + s_j^2 - r^2) + 2 a s_j < 0      ["circle condition"]
  and every bisector point of B(0,a) is in one of the disks:  for x on the bisector,
  |x| <= a and |x-h2| > r (wlog h2 far)  =>  a^2 + s_2^2 + 2 a s_2 cos(delta) <= r^2.
Controls: dense grid + SLSQP polish of m over B(0,a); and the two "naive" criteria.
"""
import numpy as np
from scipy.optimize import minimize
import sys

# ---------------- exact criterion ----------------
def _line_cut(a, s1, s2, j):
    s = (s1, s2)[j]
    t = (s1, s2)[1-j]
    d = np.hypot(s1 - s2*np.cos(0.0), 0.0)  # placeholder, replaced below
    return None

def M_exact(a, s1, s2, delta, j):
    """exact max of |x-h_j| over B(0,a) cap C_j; returns (value, which-part)."""
    s = (s1, s2)[j]; t = (s1, s2)[1-j]
    if s <= 0.0:
        return a, 'hub-at-centre'
    L = np.hypot(s1 - s2*np.cos(delta), s2*np.sin(delta))  # = |h1-h2|
    bound = a + s
    part = 'circle'
    if L > 1e-300:
        n = (a*a + s*s - t*t)/2.0
        if n*n < a*a*L*L:                      # bisector line cuts B(0,a)
            c = n/L
            v = c + np.sqrt(max(a*a - n*n/(L*L), 0.0))
            if v > bound:
                bound = v; part = 'bisector'
            else:
                part = 'circle'
    return bound, part

def core_covered_exact(a, r, s1, s2, delta):
    M0, _ = M_exact(a, s1, s2, delta, 0)
    M1, _ = M_exact(a, s1, s2, delta, 1)
    return (M0 <= r + 1e-13) and (M1 <= r + 1e-13), max(M0, M1)

# ---------------- "naive" criteria for comparison ----------------
def circle_criterion(a, r, s1, s2, delta):
    if s1 <= 0 or s2 <= 0:
        return True
    b1 = np.arccos(np.clip((a*a+s1*s1-r*r)/(2*a*s1), -1, 1))
    b2 = np.arccos(np.clip((a*a+s2*s2-r*r)/(2*a*s2), -1, 1))
    return b1 + b2 >= 2*np.pi - delta - 1e-13

def product_criterion(a, r, s1, s2, delta):
    return s1*s2 <= r*r - a*a + 1e-13

# ---------------- numeric truth ----------------
def core_gap_numeric(a, r, s1, s2, delta, ngrid=201, nang=1201):
    h1 = np.array([s1, 0.0]); h2 = np.array([s2*np.cos(delta), s2*np.sin(delta)])
    rs = np.linspace(0.0, a, ngrid); th = np.linspace(0.0, 2*np.pi, nang, endpoint=False)
    R, T = np.meshgrid(rs, th, indexing='ij')
    X = R*np.cos(T); Y = R*np.sin(T)
    M = np.minimum(np.hypot(X-h1[0], Y-h1[1]), np.hypot(X-h2[0], Y-h2[1]))
    k = np.unravel_index(np.argmax(M), M.shape); x0 = np.array([X[k], Y[k]]); best = M[k]
    def negm(x): return -min(np.hypot(*(x-h1)), np.hypot(*(x-h2)))
    for st in (x0, np.zeros(2), a*np.array([np.cos(0.7), np.sin(0.7)])):
        try:
            res = minimize(negm, st, method='SLSQP',
                           constraints=[{'type':'ineq','fun':lambda x: a*a-x[0]**2-x[1]**2}],
                           options={'ftol':1e-14,'maxiter':400})
            if -res.fun > best: best = -res.fun; x0 = res.x
        except Exception:
            pass
    return best, x0

def run_verify(r=0.38, ntest=400, seed=1):
    a = 1.0-2*r; rng = np.random.default_rng(seed); worst = 0.0; bad = []
    for _ in range(ntest):
        s1 = rng.uniform(0.0, 1.0-r); s2 = rng.uniform(0.0, 1.0-r); delta = rng.uniform(0.0, np.pi)
        ok, me = core_covered_exact(a, r, s1, s2, delta)
        mn, xm = core_gap_numeric(a, r, s1, s2, delta, ngrid=141, nang=841)
        err = abs(me-mn); worst = max(worst, err)
        if err > 4e-3 or (ok != (mn <= r)):
            bad.append((s1, s2, delta, me, mn, err, ok, mn <= r))
    print(f"[verify] r={r} a={a:.6f} n={ntest}  max|M_exact - numeric| = {worst:.3e}   mismatches={len(bad)}")
    for b in bad[:8]:
        print("   MISMATCH s1=%.6f s2=%.6f delta=%.6f exact=%.6f num=%.6f err=%.2e ok=%s numok=%s" % b)
    return worst, bad

if __name__ == "__main__":
    r = 0.38; a = 1-2*r
    print("="*100)
    print("A. exact criterion vs numeric truth (random hub configurations)")
    print("="*100)
    run_verify(r=r, ntest=int(sys.argv[1]) if len(sys.argv) > 1 else 400)
    print()
    print("="*100)
    print("B. candidate criteria at test configurations (delta = pi unless stated)")
    print("="*100)
    tests = [(0.2946,0.14,np.pi),(0.2946,0.2946,np.pi),(0.2946,0.2946,2.0),(0.29,0.29,np.pi),
             (0.29,0.29,2.3),(0.29,0.29,2.5),(0.14,0.14,np.pi),(0.26,0.26,np.pi),(0.27,0.26,np.pi),
             (0.24,0.14,np.pi),(0.20,0.30,np.pi),(0.10,0.60,np.pi),(0.14,0.62,np.pi),
             (0.05,0.50,np.pi),(0.00,0.30,np.pi),(0.2946,0.2946,1.5),(0.2946,0.2946,1.0)]
    for (s1,s2,d) in tests:
        ok,me = core_covered_exact(a,r,s1,s2,d)
        mn,xm = core_gap_numeric(a,r,s1,s2,d,ngrid=161,nang=961)
        c1,_ = M_exact(a,s1,s2,d,0); c2,_ = M_exact(a,s1,s2,d,1)
        print(f" s1={s1:.4f} s2={s2:.4f} d={d:.3f} | M1={c1:.5f} M2={c2:.5f} | EXACT-disk={str(ok):5s} "
              f"(num max m={mn:.5f}) | circle-crit={circle_criterion(a,r,s1,s2,d)!s:5s} "
              f"| product={product_criterion(a,r,s1,s2,d)!s:5s}")
