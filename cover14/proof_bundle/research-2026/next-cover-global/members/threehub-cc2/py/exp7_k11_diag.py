# -*- coding: utf-8 -*-
"""
exp7_k11_diag.py -- members/threehub-cc2

DIAGNOSIS of the k=11 optimum found with the corrected 2D criterion (exp6: ~0.3517).
Questions:
  Q1 does the best k=11 configuration's 11 ACTIVE centres cover S1 by themselves?
     (if yes, the obstruction is in the middle annulus / hub layer; if no, it is the
      boundary ring)
  Q2 how much does the boundary ring alone cost: min over 11-ring configurations
     (all radii = 1) of max[min over S1]?   That is the pure 11-arc covering radius.
  Q3 what is the minimal radius r such that 14 disks cover D with the activity split
     11/3 NOT imposed (free search)?  (comparison: the saved k=10 cover at U)
  Q4 the middle-annulus capacity: the annulus {2r <= |x| <= 1-2r} is at distance > r
     from every hub (|x-h| >= |x|-|h| >= 2U-U = U > r), so it must be covered by the
     11 active disks alone.  Measure the annulus covering radius with 11 centres in
     the annulus [1-r, 1+r].
"""
import json, math, time
import numpy as np
from fractions import Fraction as F

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U
NACT = 11


def grid2d(n):
    xs = np.linspace(-1.0, 1.0, n)
    X, Y = np.meshgrid(xs, xs)
    m = X * X + Y * Y <= 1.0 + 1e-12
    return np.stack([X[m], Y[m]], axis=1)


def annulus_pts(rmin, rmax, nth=720, nr=40):
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    rr = np.linspace(rmin, rmax, nr)
    TT, RT = np.meshgrid(th, rr)
    return np.stack([(RT * np.cos(TT)).ravel(), (RT * np.sin(TT)).ravel()], axis=1)


def maxmin(pts, C):
    C = np.asarray(C, float)
    d = np.sqrt(((pts[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    k = int(np.argmax(d))
    return float(d[k]), pts[k].tolist()


TH = np.linspace(0, 2 * math.pi, 8000, endpoint=False)
S1 = np.stack([np.cos(TH), np.sin(TH)], axis=1)
PF = grid2d(601)
rng = np.random.default_rng(777)

print("=== Q2  pure 11-arc covering of S1 (centres all at radius rho) ===")
for rho in [1.0, 1.05, 1.1, 1.2]:
    best = 1e9
    for _ in range(4):
        ang = np.sort(rng.random(NACT) * 2 * math.pi)
        C = np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)
        f = maxmin(S1, C)[0]
        step = 0.15
        for it in range(6000):
            T = 0.002 * (1 - it / 6000) + 1e-12
            C2 = C.copy()
            k = int(rng.integers(0, NACT))
            ang2 = math.atan2(C2[k, 1], C2[k, 0]) + step * rng.normal()
            C2[k] = (rho * math.cos(ang2), rho * math.sin(ang2))
            f2 = maxmin(S1, C2)[0]
            if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
                C, f = C2, f2
            if it % 1500 == 1499:
                step *= 0.7
        best = min(best, f)
    print(f"  rho={rho:.3f}: min max-min on S1 = {best:.9f}  ({best-U:+.3e} vs U)")

print()
print("=== Q4  middle annulus {2U <= |x| <= 1-2U} covered by 11 centres in [1-U,1+U] ===")
AP = annulus_pts(2 * U, A)
print(f"  annulus radii: {2*U:.6f} .. {A:.6f}; samples {len(AP)}")


def ann_search(iters=6000):
    ang = np.sort((np.arange(NACT) + 0.3 * rng.random(NACT)) * 2 * math.pi / NACT)
    rho = np.full(NACT, 1.0)
    C = np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)
    f = maxmin(AP, C)[0]
    step = 0.15
    for it in range(iters):
        T = 0.002 * (1 - it / iters) + 1e-12
        C2 = C.copy()
        k = int(rng.integers(0, NACT))
        u = rng.random()
        r0 = math.hypot(*C2[k])
        a0 = math.atan2(C2[k, 1], C2[k, 0])
        if u < 0.6:
            a0 += step * rng.normal()
        else:
            r0 = min(max(r0 + step * rng.normal(), INACT), 1.0 + U)
        C2[k] = (r0 * math.cos(a0), r0 * math.sin(a0))
        f2 = maxmin(AP, C2)[0]
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            C, f = C2, f2
        if it % 1500 == 1499:
            step *= 0.7
    return C, f


bestA = None
for _ in range(4):
    C, f = ann_search()
    if bestA is None or f < bestA[0]:
        bestA = (f, C)
print(f"  best annulus covering radius with 11 active centres = {bestA[0]:.9f}  "
      f"({bestA[0]-U:+.3e} vs U), worst pt {[round(q,6) for q in maxmin(AP, bestA[1])[1]]}")

print()
print("=== Q1  the exp6 best configuration: can its 11 active centres cover S1 alone? ===")
best = json.load(open("research-2026/next-cover-global/members/threehub-cc2/evidence/"
                      "exp6_k11_2d.json"))["best"]
act = np.array([[float(x) for x in a] for a in best["hub"]])
print("  (exp6 stored hub only in 'best'; recomputing from hub/active files not stored)")
print()
print("=== Q3  free 14-centre search, activity split free, 2D criterion ===")


def free_search(iters=8000, seed14=None):
    if seed14 is None:
        ang = np.sort(rng.random(14) * 2 * math.pi)
        rho = 0.3 + 1.2 * rng.random(14)
    else:
        ang = np.sort(np.arctan2(seed14[:, 1], seed14[:, 0]))
        rho = np.linalg.norm(seed14, axis=1)
    C = np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)
    f = maxmin(PF, C)[0]
    step = 0.1
    for it in range(iters):
        T = 0.003 * (1 - it / iters) + 1e-12
        C2 = C.copy()
        k = int(rng.integers(0, 14))
        r0 = math.hypot(*C2[k]); a0 = math.atan2(C2[k, 1], C2[k, 0])
        if rng.random() < 0.65:
            a0 += step * rng.normal()
        else:
            r0 = min(max(r0 + step * rng.normal(), 0.0), 2.0)
        C2[k] = (r0 * math.cos(a0), r0 * math.sin(a0))
        f2 = maxmin(PF, C2)[0]
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            C, f = C2, f2
        if it % 2000 == 1999:
            step *= 0.75
    return C, f


d0 = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d0["centers"]])
C, f = free_search(seed14=Csav)
nrm = np.linalg.norm(C, axis=1)
print(f"  from the saved construction: f={f:.9f}  activity count |c|>=1-U: "
      f"{int((nrm >= INACT).sum())}")
C, f = free_search()
nrm = np.linalg.norm(C, axis=1)
print(f"  from a random start:        f={f:.9f}  activity count |c|>=1-U: "
      f"{int((nrm >= INACT).sum())}")
