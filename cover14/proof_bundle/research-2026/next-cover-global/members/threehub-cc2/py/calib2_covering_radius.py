# -*- coding: utf-8 -*-
"""
calib2_covering_radius.py -- members/threehub-cc2  (v2, fast evaluator)

INSTRUMENT (correct normalisation).
  Clipped covering criterion: for a finite family of closed disks B(c_i,r),
        D subset of union_i B(c_i,r)   <=>   S1 subset of union_i B(c_i,r).
  Reason: if x is uncovered, move radially outward; the first uncovered boundary
  point is reached by closedness.  Hence the covering radius of D by centres C is
        coverD(C) = max_{theta} min_i |(cos,sin)(theta) - c_i| ,
  which is what is computed here on a dense theta grid (3600 points).  The interior is
  cheched separately (polar grid) only for final candidates, as an audit.

CONTROLS (analytic, this is the point of the file)
  * regular n-gon ring, optimal t = 1/(2 sin(pi/n)):  coverD = 1/(2 cos(pi/(2n)))
      n=3 -> 0.577350, n=4 -> 0.707107, n=5 -> 0.809017, n=14 -> 0.496163
  * n=3 absolute: r_3 = sqrt 3 (3-fold rotation forces a centre at 0, or a
    three-arc argument); n=4: r_4 = sqrt 2.
  * the saved rational construction (lead/improved-upper-test.json) must have
    coverD <= 0.3317320342762341... at its own resolution (reproduces the C411 /
    improved-upper computation).
"""
import json, math, sys
from fractions import Fraction as F
import numpy as np

U = 0.33173203427623414
NTH = 3600
TH = np.linspace(0.0, 2 * math.pi, NTH, endpoint=False)
CS, SN = np.cos(TH), np.sin(TH)


def coverD(C):
    """max over S1 of distance to nearest centre."""
    C = np.asarray(C, float)
    dx = CS[:, None] - C[None, :, 0]
    dy = SN[:, None] - C[None, :, 1]
    d = np.sqrt(dx * dx + dy * dy).min(axis=1)
    k = int(np.argmax(d))
    return float(d[k]), (float(CS[k]), float(SN[k]))


def interior_audit(C, nth=720, nr=160):
    """sampled max over the closed disk of the nearest-centre distance (validates the
    S1-clipped criterion).  Coarser than coverD; used for final candidates only."""
    C = np.asarray(C, float)
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    rr = np.linspace(1.0, 0.0, nr)
    TT, RT = np.meshgrid(th, rr)
    P = np.stack([(RT * np.cos(TT)).ravel(), (RT * np.sin(TT)).ravel()], axis=1)
    d = np.sqrt(((P[:, None, :] - C[None, :, :]) ** 2).sum(axis=2))
    dmin = d.min(axis=1)
    k = int(np.argmax(dmin))
    return float(dmin[k]), P[k].tolist()


def ring(n, t):
    a = 2 * math.pi * np.arange(n) / n
    return np.stack([t * np.cos(a), t * np.sin(a)], axis=1)


print("=== control 1: optimal regular n-gon ring; theory 1/(2cos(pi/2n)) ===")
for n in [3, 4, 5, 6, 7, 8, 14]:
    t = 1.0 / (2 * math.sin(math.pi / n))
    v, wp = coverD(ring(n, t))
    print(f"  n={n:2d} t*={t:.6f} coverD={v:.6f} theory={1/(2*math.cos(math.pi/(2*n))):.6f}"
          f" worst={tuple(round(q,4) for q in wp)}")
sys.stdout.flush()

rng = np.random.default_rng(20260924)


def optimise(n, iters=30000, starts=20, rad_lo=0.3, rad_hi=2.5):
    """hillclimb on 2n polar coordinates."""
    best, bestC = 1e9, None
    for s in range(starts):
        rr = rad_lo + (rad_hi - rad_lo) * rng.random(n)
        aa = np.sort(rng.random(n) * 2 * math.pi)
        C = np.stack([rr * np.cos(aa), rr * np.sin(aa)], axis=1)
        v, _ = coverD(C)
        step = 0.2
        for it in range(iters):
            T = 0.01 * (1 - it / iters) + 1e-7
            C2 = C.copy()
            if rng.random() < 0.3:
                k = int(rng.integers(0, n))
                nv = math.hypot(*C2[k]) + step * rng.normal()
                nv = min(max(nv, rad_lo), rad_hi)
                ang = math.atan2(C2[k, 1], C2[k, 0])
                C2[k] = (nv * math.cos(ang), nv * math.sin(ang))
            else:
                k = int(rng.integers(0, n))
                ang = math.atan2(C2[k, 1], C2[k, 0]) + step * rng.normal()
                nv = math.hypot(*C2[k])
                C2[k] = (nv * math.cos(ang), nv * math.sin(ang))
            v2, _ = coverD(C2)
            if v2 < v - 1e-13 or rng.random() < math.exp(-(v2 - v) / T):
                C, v = C2, v2
            if it % 3000 == 2999:
                step *= 0.65
        if v < best:
            best, bestC = v, C
    return best, bestC


print()
print("=== control 2: multistart hillclimb vs analytic optima ===")
for n, th in [(3, math.sqrt(3.0)), (4, math.sqrt(2.0)), (5, None)]:
    v, C = optimise(n, starts=15, iters=20000)
    s = "%.6f" % th if th else "-"
    print(f"  n={n} hillclimb coverD={v:.6f}  known={s}  diff="
          f"{(v-th) if th else float('nan'):+.5f}")
    sys.stdout.flush()

print()
print("=== control 3: saved rational construction, lead/improved-upper-test.json ===")
d = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
C = np.array([[float(F(x[0])), float(F(x[1]))] for x in d["centers"]])
v, wp = coverD(C)
vi, wpi = interior_audit(C)
print(f"  n={len(C)}  coverD(S1 grid, {NTH}) = {v:.12f}")
print(f"  interior audit         = {vi:.12f} at {tuple(round(q,6) for q in wpi)}")
print(f"  its own rational threshold = {d['threshold_decimal']}")
print(f"  difference coverD - threshold = {v - float(F(d['threshold'])):+.3e}  (grid)")
print(f"  largest |c| = {max(math.hypot(*q) for q in C):.9f}   1-U = {1-U:.9f}")
print(f"  count |c| >= 1-U : {sum(1 for q in C if math.hypot(*q) >= 1-U)}")
