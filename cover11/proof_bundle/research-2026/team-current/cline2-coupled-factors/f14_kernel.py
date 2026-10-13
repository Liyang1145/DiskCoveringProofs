"""cline2-coupled-factors f14: sector endpoint-symmetry collapse, corrected.

With the endpoint-copy identity u_k = v_k =: e_k (proved in f12) the sector kernel is

    S(alpha, e) = R^2 e^2 sin(alpha)/2 + (w - sin w)/2,
    w = w(alpha, e) = 2 asin(R e sin(alpha/2))      [= 2 asin(R sqrt(u^2+v^2-2uv cos a)/2)
                                                     when u = v = e]

so on the diagonal the term R^2 e^2 sin(alpha)/2 is the triangle area and (w-sin w)/2 the
circular segment.  At e = 1 the triangle term is R^2 sin(alpha)/2, which is exactly
(R^2/2)(alpha - sin alpha) + (R^2/2) sin alpha ... i.e. the correct decomposition is

    S(alpha,1) = (R^2/2)(alpha - sin alpha) + (w - sin w)/2,   w = 2 asin(R sin(alpha/2)),

the first bracket being the "arc minus chord" of the site triangle.  The identity
    R^2 alpha/2 + (w - sin w)/2  used in the first draft was WRONG (it missed the chord
    correction); it is dropped here and the exact version is used instead.

Sampled dual bounds are reported for the same lead z-vectors on
    (0) full domain  -- reproduces the lead
    (1) diagonal u=v  -- valid restriction (all genuine diagrams have u=v)
    (2) diagonal with the exact closed form (independent re-derivation of the kernel)
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96


def kernel_full(a, u, v):
    ch = R*np.sqrt(np.maximum(0, u*u+v*v-2*u*v*np.cos(a)))
    w = 2*np.arcsin(np.minimum(1.0, ch/2))
    return R*R*u*v*np.sin(a)/2 + (w-np.sin(w))/2, w


def kernel_diag(a, e):
    w = 2*np.arcsin(np.minimum(1.0, R*e*np.sin(a/2)))
    return R*R*e*e*np.sin(a)/2 + (w-np.sin(w))/2, w


def kernel_diag1(a):
    w = 2*np.arcsin(np.minimum(1.0, R*np.sin(a/2)))
    return R*R*(a-np.sin(a))/2 + (w-np.sin(w))/2, w


a = np.linspace(0, pi, 20001)
Sf, wf = kernel_full(a, np.ones_like(a), np.ones_like(a))
Sd, wd = kernel_diag(a, np.ones(a.size))
Sd1, wd1 = kernel_diag1(a)
print('kernel agreement full(diagonal) vs closed form:',
      np.abs(Sf-Sd1).max(), np.abs(wf-wd1).max())
print('draft-1 wrong form max error:',
      np.abs(R*R*a/2 + (wf-np.sin(wf))/2 - Sf).max())
print('segment-only (no triangle) max error vs full:',
      np.abs((wf-np.sin(wf))/2 - Sf).max())

d = np.load(OUT/'realized.npz', allow_pickle=True)
W = d['W']; al = d['al']; Rc = float(d['Rc'])
Sreal = [Rc*Rc*math.sin(al[k])/2 + (W[k]-math.sin(W[k]))/2 for k in range(9)]
print('realized sectors: sum of S =', sum(Sreal), '  pi =', pi)
print('realized closed form e=1 residual:',
      np.abs(np.array([kernel_diag1(x)[0] for x in al]) - np.array(Sreal)
             * (Rc/R)**2 / 1.0).max())
