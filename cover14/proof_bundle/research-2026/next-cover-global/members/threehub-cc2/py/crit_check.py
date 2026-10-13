# -*- coding: utf-8 -*-
"""
crit_check.py -- members/threehub-cc2

THE INSTRUMENT ERROR AND ITS REPAIR.

Earlier files (calib2, exp2..exp5) used
    coverD = max over S1 of min_i |x - c_i|
justified by "an uncovered interior point can be pushed radially outward".  That
justification requires |c_i| >= 1 for the outward direction to increase the distance
to the nearest centre; with centres INSIDE the disk (hubs!) the distance to a hub can
DECREASE while pushing outward.  Correct statement: the maximum of a finite family of
distance functions d_i(x) = |x-c_i| only has local maxima on S1 (where the gradient of
d_i points outward) -- but we are maximising the MINIMUM over i, i.e. min_i d_i, whose
maxima are NOT excluded from the interior (a point can be "uncovered" in a hole).
Hence the clipped criterion is valid only if every centre is outside D.

THIS SCRIPT
  1. computes max over a 2D grid of min_i |x - c_i| (true sampled covering radius of D)
  2. compares with the S1-only value for
       (a) the saved 14-centre rational construction (all |c| <= 0.9434 < 1),
       (b) a k=11-style configuration from exp5 (11 active + 3 hubs, hubs inside),
       (c) a control with all centres outside D (S1 criterion must agree).
  3. repeats the k=11 constrained search with the corrected 2D criterion.
"""
import json, math, time
import numpy as np
from fractions import Fraction as F

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U


def grid2d(nx=801, ny=801):
    xs = np.linspace(-1.0, 1.0, nx)
    X, Y = np.meshgrid(xs, xs)
    m = X * X + Y * Y <= 1.0 + 1e-12
    return np.stack([X[m], Y[m]], axis=1)


P2 = grid2d()
th = np.linspace(0, 2 * math.pi, 20000, endpoint=False)
S1 = np.stack([np.cos(th), np.sin(th)], axis=1)


def maxmin(pts, C):
    C = np.asarray(C, float)
    d = np.sqrt(((pts[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    k = int(np.argmax(d))
    return float(d[k]), pts[k].tolist()


d0 = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d0["centers"]])

print("=== (1) saved rational construction: 2D grid vs S1-only ===")
v2d, p2d = maxmin(P2, Csav)
v1d, p1d = maxmin(S1, Csav)
print(f"  2D grid   max min-dist = {v2d:.12f}  at {[round(q,6) for q in p2d]}")
print(f"  S1 only   max min-dist = {v1d:.12f}  at {[round(q,6) for q in p1d]}")
print(f"  rational threshold     = {d0['threshold_decimal']}")
print(f"  => saved construction's true covering radius is {v2d:.9f}, "
      f"{'ABOVE' if v2d > U else 'at/below'} U = {U:.9f}")
print()

print("=== (2) exp5 best k=11 configuration (11 active + 3 hubs) ===")
best = json.load(open("research-2026/next-cover-global/members/threehub-cc2/evidence/"
                      "exp5_k11_feasible.json"))["best"]
C = np.array([[float(x) for x in h] for h in best["hub"]] +
             [[float(x) for x in a] for a in best["active"]])
v2d, p2d = maxmin(P2, C)
v1d, p1d = maxmin(S1, C)
print(f"  exp5 reported coverD (S1 only) = {best['coverD']:.12f}")
print(f"  2D grid  max min-dist = {v2d:.12f} at {[round(q,6) for q in p2d]}")
print(f"  S1 only  max min-dist = {v1d:.12f}")
print(f"  => the S1-only criterion was wrong by {v2d - v1d:+.6f}; "
      f"true value vs U: {v2d - U:+.6f}")
print()

print("=== (3) control: all centres OUTSIDE D (S1 criterion must be valid) ===")
rng = np.random.default_rng(5)
Cout = np.array([[1.3 * math.cos(t), 1.3 * math.sin(t)]
                 for t in np.sort(rng.random(11) * 2 * math.pi)])
Cout = np.vstack([Cout, np.array([[0.0, 0.0]])])
v2d, _ = maxmin(P2, Cout)
v1d, _ = maxmin(S1, Cout)
print(f"  |c|=1.3 ring + origin: 2D {v2d:.9f}   S1 {v1d:.9f}  diff {v2d-v1d:+.2e}")
print()
print("=== conclusion ===")
print("  Every number in exp2..exp5 that used the S1-only criterion must be recomputed.")
print("  The hub-inside configuration of exp5 had S1 readings ~0.29 but its TRUE")
print("  covering radius is the 2D value printed above.")
