# -*- coding: utf-8 -*-
"""o1_hole_circle.py -- stronger sufficient mechanism (bounded, numeric).

Criterion (lead): if the hole contains a full disk B(z,s) with s > r, then two radius-r
disks cannot cover the hole (a radius-r disk cuts a circle of radius s > r in an arc of
measure <= 2 asin(r/s) < pi, so two of them leave a point of that circle uncovered).
Implement as the 2-D max-min problem
      maximise  d(z) = min_i |z - c_i|        subject to   |z| + (d(z) - r) <= 1 ,
and test  d(z*) - r > r  i.e.  d(z*) > 2r  (so the hole contains a disk of radius > r).

Controls / objects:
  (C1) the certified O1 counterexample ledger  (expect d* ~ 0.83 > 0.76);
  (C2) the triple-common-point family of o1_triple_common.py (maximal six fillers, random
       cluster sharing a point p) -- report the distribution of d* - 2r and the hardest case.

No lower-bound claim is made from this numeric probe; if d* <= 2r somewhere that is a
METHOD GAP (it neither proves extendability nor refutes the triple exclusion).
"""
import importlib.util
import json
import math
import os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
R = 0.38
spec = importlib.util.spec_from_file_location("otc", os.path.join(HERE, "o1_triple_common.py"))
otc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(otc)


def d_of_z(C, X, Y):
    d = np.full(X.shape, 1e9)
    for (cx, cy) in C:
        d = np.minimum(d, np.sqrt((X - cx) ** 2 + (Y - cy) ** 2))
    return d


def maxmin_circle(C, nz=400, nt=800, refine=6):
    """maximise d(z) subject to |z| + d(z) - r <= 1 by grid + local refine (multi-seed)."""
    zr = (np.arange(nz) + 0.5) / nz
    zt = 2 * math.pi * (np.arange(nt) + 0.5) / nt
    X = np.outer(zr, np.cos(zt)).ravel()
    Y = np.outer(zr, np.sin(zt)).ravel()
    D = d_of_z(C, X, Y)
    Rn = np.hypot(X, Y)
    feas = (Rn + D - R) <= 1.0
    # take the best few feasible seeds
    order = np.argsort(-np.where(feas, D, -1))
    best = (-1.0, None)
    for seed in order[:40]:
        z = np.array([X[seed], Y[seed]])
        step = 0.02
        for it in range(200):
            cand = []
            for dx in (-step, 0, step):
                for dy in (-step, 0, step):
                    zz = z + np.array([dx, dy])
                    d = min(math.dist(zz, c) for c in C)
                    if math.hypot(*zz) + d - R <= 1.0:
                        cand.append((d, zz))
            if not cand:
                break
            cand.sort(key=lambda t: -t[0])
            if cand[0][0] <= min(math.dist(z, c) for c in C) + 1e-15:
                step *= 0.5
                if step < 1e-6:
                    break
            z = cand[0][1]
        d = min(math.dist(z, c) for c in C)
        if d > best[0]:
            best = (d, z)
    return best


def control_certified():
    d = json.load(open(os.path.join(OUT, "o1_certificate.json"), encoding="utf-8"))
    C = []
    for k in range(9):
        pass
    # rebuild centres from the certificate data (same construction as o1_certify)
    import sys
    sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-20260923\lambda5\py")
    import rt_iv as K
    from fractions import Fraction as F
    K._init_pi()
    r = F(19, 50)
    t = [F(40279, 125000), F(97449, 250000), F(21723, 62500)] + [F(38979, 10 ** 5)] * 6
    orat = [F(512993, 10 ** 6)] + [F(1, 10 ** 6)] * 7
    s = 2 * sum(t) - sum(orat)
    o8 = (s - 2 * K.PI_HI, s - 2 * K.PI_LO)
    ph = [F(0)]
    for k in range(8):
        ph.append(ph[-1] + t[k] + t[(k + 1) % 9] - orat[k])
    for k in range(9):
        c, ss = K.sin_cos_iv(t[k], t[k])
        s2 = K.iv_sqr(ss)
        rad = (r * r - s2[1], r * r - s2[0])
        rho = K.iv_sub(c, K.iv_sqrt(rad))
        cph, sph = K.sin_cos_iv(ph[k], ph[k])
        C.append((float(rho[0] * cph[0]), float(rho[0] * sph[0])))
    return C


if __name__ == "__main__":
    print("=" * 78)
    print("hole-circle criterion: maximise d(z)=min_i|z-c_i| s.t. |z|+d(z)-r <= 1")
    print("criterion for non-extendability: d* > 2r = %.6f (hole contains a disk of radius > r)" % (2 * R))
    print("=" * 78)
    C = control_certified()
    d, z = maxmin_circle(C)
    print("CONTROL certified O1 ledger : d* = %.9f  at z = (%.6f, %.6f) ; d* - 2r = %+.6f"
          % (d, z[0], z[1], d - 2 * R))
    print("   hole disk radius s = d* - r = %.9f > r = %.6f ? %s ; |z| + s = %.6f <= 1 ? %s"
          % (d - R, R, d - R > R, math.hypot(*z) + d - R,
             math.hypot(*z) + d - R <= 1))
    print()
    rng = np.random.default_rng(11)
    rows = []
    tried = 0
    while len(rows) < 60 and tried < 4000:
        tried += 1
        rp = rng.uniform(1 - 2 * R, 0.99)
        thp = rng.uniform(0, 2 * math.pi)
        p = (rp * math.cos(thp), rp * math.sin(thp))
        angles = rng.uniform(0, 2 * math.pi, 3)
        C2, info, ok = otc.build_ledger(p, angles)
        if not ok:
            continue
        d, z = maxmin_circle(C2, nz=220, nt=440, refine=4)
        rows.append((d - 2 * R, d, z, info, p, C2))
    rows.sort(key=lambda t: t[0])
    ms = np.array([t[0] for t in rows])
    print("triple-common-point family (maximal six fillers): %d legal sampled ledgers" % len(rows))
    for q in (0, 5, 25, 50, 75, 95, 100):
        print("   d* - 2r  q%3d%% = %+.6f" % (q, float(np.percentile(ms, q))))
    worst = rows[0]
    print()
    print("HARDEST sampled triple-common ledger: d* - 2r = %+.6f  (d* = %.6f, z = (%.6f, %.6f))"
          % (worst[0], worst[1], worst[2][0], worst[2][1]))
    print("   p = (%.6f, %.6f) ; S = %.6f ; t_cluster(deg) = %s"
          % (worst[4][0], worst[4][1], worst[3][3], ["%.4f" % math.degrees(x) for x in worst[3][0]]))
    print("   six-filler core distance = %.6f (must be >= rho0-r = %.6f)"
          % (min(math.hypot(*c) for c in worst[5][3:]), otc.RHO0 - R))
    npos = int((ms > 0).sum())
    print("   ledgers with d* > 2r : %d / %d  (all sampled? %s)" % (npos, len(rows), npos == len(rows)))
    out = dict(r=R, criterion="hole contains a disk of radius > r  <=>  d* > 2r",
               control_certified=dict(dstar=d, z=list(z), dstar_minus_2r=d - 2 * R),
               family=dict(n=len(rows), n_positive=npos, tried=tried,
                           margins=[float(t[0]) for t in rows],
                           hardest=dict(margin=float(worst[0]), dstar=float(worst[1]),
                                        z=[float(worst[2][0]), float(worst[2][1])],
                                        p=list(worst[4]), S=float(worst[3][3]),
                                        t_cluster=[float(x) for x in worst[3][0]])),
               note="numeric probe; d* <= 2r anywhere is a METHOD GAP (no extendability "
                    "claim, no refutation of the triple exclusion)")
    with open(os.path.join(OUT, "o1_hole_circle.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print("wrote out/o1_hole_circle.json")
