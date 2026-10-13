# -*- coding: utf-8 -*-
"""
diag3.py -- members/threehub-cc2  (only the free-14 control that diag2 did not reach)

Q: with the corrected 2D criterion, does a free 14-centre search respect the saved
   value 0.331732034276, and how many centres end up active (|c| >= 1-U)?
"""
import json, math
import numpy as np
from fractions import Fraction as F

U = 0.33173203427623414
INACT = 1.0 - U
rng = np.random.default_rng(1618)


def grid2d(n):
    xs = np.linspace(-1.0, 1.0, n)
    X, Y = np.meshgrid(xs, xs)
    m = X * X + Y * Y <= 1.0 + 1e-12
    return np.stack([X[m], Y[m]], axis=1)


def maxmin(pts, C, chunk=40000):
    C = np.asarray(C, float)
    best, bp = -1.0, None
    for i in range(0, len(pts), chunk):
        P = pts[i:i + chunk]
        d = np.sqrt(((P[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
        k = int(np.argmax(d))
        if float(d[k]) > best:
            best, bp = float(d[k]), P[k].tolist()
    return best, bp


PF = grid2d(501)
d0 = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d0["centers"]])
print("saved construction, 2D(501):", maxmin(PF, Csav)[0])
print("saved activity count |c|>=1-U:", int((np.linalg.norm(Csav, axis=1) >= INACT).sum()),
      "  (its 4 largest norms are 0.7808,0.8916,0.9434 and 0.8916 - all < 1-U)")


def free14(C0, iters=4000):
    C = np.array(C0, float)
    f = maxmin(PF, C)[0]
    step = 0.08
    for it in range(iters):
        T = 0.003 * (1 - it / iters) + 1e-12
        C2 = C.copy()
        k = int(rng.integers(0, 14))
        r0 = math.hypot(*C2[k]); a0 = math.atan2(C2[k, 1], C2[k, 0])
        if rng.random() < 0.7:
            a0 += step * rng.normal()
        else:
            r0 = min(max(r0 + step * rng.normal(), 0.0), 2.0)
        C2[k] = (r0 * math.cos(a0), r0 * math.sin(a0))
        f2 = maxmin(PF, C2)[0]
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            C, f = C2, f2
        if it % 1000 == 999:
            step = max(step * 0.8, 1e-5)
    return C, f


C, f = free14(Csav)
nrm = np.linalg.norm(C, axis=1)
print(f"from saved:   f={f:.9f}  activity={int((nrm>=INACT).sum())}  norms="
      f"{[round(float(q),4) for q in sorted(nrm)]}")
for seed in range(3):
    ang = np.sort(rng.random(14) * 2 * math.pi)
    C0 = np.stack([np.linspace(0.4, 1.3, 14) * np.cos(ang),
                   np.linspace(0.4, 1.3, 14) * np.sin(ang)], axis=1)
    C0 = np.stack([(0.3 + 1.2 * rng.random(14)) * np.cos(ang),
                   (0.3 + 1.2 * rng.random(14)) * np.sin(ang)], axis=1)
    C, f = free14(C0)
    nrm = np.linalg.norm(C, axis=1)
    print(f"random {seed}:  f={f:.9f}  activity={int((nrm>=INACT).sum())}")
