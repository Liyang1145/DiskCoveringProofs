# -*- coding: utf-8 -*-
"""
diag2.py -- members/threehub-cc2   (memory-safe maxmin, chunked)

A. pure 11-arc covering radii of S1 (centres at radius rho):  min max-min on S1
B. middle-annulus capacity: {2r <= |x| <= 1-2r} must be covered by the 11 active
   disks alone (hubs are at distance >= |x|-|h| >= 2r - r = r), centres in [1-r,1+r]
C. free 14-centre search from the saved construction (control) and from random starts
D. the two-island bound assembly:  min r such that an 11-active configuration with
   centres in [1-r,1+r] covers S1 AND the annulus [2r, 1-2r]
"""
import math, json
import numpy as np
from fractions import Fraction as F

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U
NACT = 11
rng = np.random.default_rng(2718)


def maxmin(pts, C, chunk=40000):
    C = np.asarray(C, float)
    best, bp = -1.0, None
    for i in range(0, len(pts), chunk):
        P = pts[i:i + chunk]
        d = np.sqrt(((P[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
        k = int(np.argmax(d))
        if d[k] > best:
            best, bp = float(d[k]), P[k].tolist()
    return best, bp


TH = np.linspace(0, 2 * math.pi, 4000, endpoint=False)
S1 = np.stack([np.cos(TH), np.sin(TH)], axis=1)


def annulus(rmin, rmax, nth=720, nr=40):
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    rr = np.linspace(rmin, rmax, nr)
    TT, RT = np.meshgrid(th, rr)
    return np.stack([(RT * np.cos(TT)).ravel(), (RT * np.sin(TT)).ravel()], axis=1)


def grid2d(n):
    xs = np.linspace(-1.0, 1.0, n)
    X, Y = np.meshgrid(xs, xs)
    m = X * X + Y * Y <= 1.0 + 1e-12
    return np.stack([X[m], Y[m]], axis=1)


def pol(ang, rho):
    return np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)


def climb(pts, ang, rho, iters, lo, hi, step0=0.15):
    C = pol(ang, rho)
    f = maxmin(pts, C)[0]
    step = step0
    for it in range(iters):
        T = 0.002 * (1 - it / iters) + 1e-12
        C2 = C.copy()
        k = int(rng.integers(0, NACT))
        r0 = math.hypot(*C2[k]); a0 = math.atan2(C2[k, 1], C2[k, 0])
        if rng.random() < 0.65:
            a0 += step * rng.normal()
        else:
            r0 = min(max(r0 + step * rng.normal(), lo), hi)
        C2[k] = (r0 * math.cos(a0), r0 * math.sin(a0))
        f2 = maxmin(pts, C2)[0]
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            C, f = C2, f2
        if it % 1500 == 1499:
            step *= 0.75
    return C, f


print("=== A. pure 11-arc ring covering of S1 ===")
for rho in [1.0, 1.1, 1.2]:
    best = 1e9
    for s in range(3):
        ang = np.sort(rng.random(NACT) * 2 * math.pi)
        C, f = climb(S1, ang, np.full(NACT, rho), 5000, rho, rho)
        best = min(best, f)
    print(f"  rho={rho:4.2f}: min max-min on S1 = {best:.9f}   (U={U:.9f}, diff {best-U:+.3e})")

print()
print("=== B. middle annulus [2U, 1-2U] with 11 centres in [1-U, 1+U] ===")
AP = annulus(2 * U, A)
best = None
for s in range(4):
    ang = np.sort((np.arange(NACT) + 0.3 * rng.random(NACT)) * 2 * math.pi / NACT)
    C, f = climb(AP, ang, np.full(NACT, 1.0), 6000, INACT, 1.0 + U)
    if best is None or f < best[0]:
        best = (f, C)
print(f"  best annulus covering radius = {best[0]:.9f}  (U={U:.9f}, diff {best[0]-U:+.3e})")
print(f"  worst annulus point {[round(q,6) for q in maxmin(AP, best[1])[1]]}")
print(f"  centre norms: {sorted(round(float(np.hypot(*c)),4) for c in best[1])}")

print()
print("=== C. free 14-centre 2D search (control + random) ===")
PF = grid2d(401)
d0 = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d0["centers"]])
print("  saved construction, 2D(401) =", maxmin(PF, Csav)[0])


def free14(C0, iters=6000):
    C = np.array(C0, float)
    f = maxmin(PF, C)[0]
    step = 0.1
    for it in range(iters):
        T = 0.003 * (1 - it / iters) + 1e-12
        C2 = C.copy()
        k = int(rng.integers(0, 14))
        r0 = math.hypot(*C2[k]); a0 = math.atan2(C2[k, 1], C2[k, 0])
        if rng.random() < 0.7:
            a0 += step * rng.normal()
            r0 = min(max(r0, 0.0), 2.0)
        else:
            r0 = min(max(r0 + step * rng.normal(), 0.0), 2.0)
        C2[k] = (r0 * math.cos(a0), r0 * math.sin(a0))
        f2 = maxmin(PF, C2)[0]
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            C, f = C2, f2
        if it % 2000 == 1999:
            step *= 0.75
    return C, f


C, f = free14(Csav)
print(f"  from saved: f={f:.9f} activity={int((np.linalg.norm(C,axis=1)>=INACT).sum())}")
C, f = free14(pol(np.sort(rng.random(14) * 2 * math.pi), 0.3 + 1.2 * rng.random(14)))
print(f"  random:     f={f:.9f} activity={int((np.linalg.norm(C,axis=1)>=INACT).sum())}")

print()
print("=== D. two-island bound: centres in [1-r,1+r] must cover S1 and [2r,1-2r] ===")
for r in [0.30, 0.32, 0.3317, 0.34, 0.35, 0.36]:
    ann = annulus(2 * r, 1.0 - 2 * r, nth=360, nr=24)
    best = 1e9
    for s in range(2):
        ang = np.sort(rng.random(NACT) * 2 * math.pi)
        C, f = climb(ann, ang, np.full(NACT, 1.0 - r + 0.02), 3000,
                     max(0.0, 1.0 - r), 1.0 + r)
        best = min(best, f)
    print(f"  r={r:.4f}: best annulus covering radius over [2r,1-2r] = {best:.6f}  "
          f"({'OK' if best <= r else 'VIOLATION'} vs r)")
