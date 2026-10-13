"""three_hub_probe.py -- diagnostic only (NOT a proof).

Question: with r = U (n14), can three strictly inactive hubs whose disks cover the
closed core K = B(0,a) have minimum enclosing radius > U?  If yes, the proposed
"min enclosing radius <= U / d_ij <= 2U" claim is FALSE and the lead gets a
counterexample; if the optimiser never exceeds U we only have evidence.

Exact coverage check: the disks cover K iff the three covered arcs of S(0,a) cover
the circle (boundary suffices for a finite union of disks).  With arc centres equal
to the hub directions and halfwidths beta_j = acos((a^2+t^2-r^2)/(2at)) (empty when
|t-a| >= r), coverage is the exact gap condition  beta_k + beta_{k+1} >= g_k for the
cyclically ordered centres.
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

U = 0.33173203427623414
A = 1 - 2 * U
HERE = Path(__file__).resolve().parent


def beta_of(t, r):
    if t <= 0:
        return 0.0
    if abs(t - A) >= r or t + A <= r:
        return 0.0
    return math.acos(max(-1.0, min(1.0, (A * A + t * t - r * r) / (2 * A * t))))


def covering_gap(params, r):
    """max over cyclic gaps of (g_k - beta_k - beta_{k+1}); <=0 means covered."""
    t = params[0::2]
    ph = params[1::2]
    order = np.argsort(ph)
    ts = t[order]
    ps = np.sort(ph)
    bet = [beta_of(float(x), r) for x in ts]
    gaps = [ps[1] - ps[0], ps[2] - ps[1], ps[0] + 2 * math.pi - ps[2]]
    worst = -1e9
    for k in range(3):
        j = (k + 1) % 3
        worst = max(worst, gaps[k] - bet[k] - bet[j])
    return worst


def min_enclosing(hs):
    """radius of the minimum enclosing circle of three points."""
    P = np.array(hs)
    best = 1e9
    for i in range(3):
        for j in range(i + 1, 3):
            c = (P[i] + P[j]) / 2
            rr = max(np.linalg.norm(Q - c) for Q in P)
            best = min(best, rr)
    # circumcircle if the triangle is acute
    a1 = np.linalg.norm(P[1] - P[2])
    b1 = np.linalg.norm(P[0] - P[2])
    c1 = np.linalg.norm(P[0] - P[1])
    s = (a1 + b1 + c1) / 2
    u1 = P[1] - P[0]; u2 = P[2] - P[0]
    area2 = abs(u1[0] * u2[1] - u1[1] * u2[0])
    if area2 > 1e-14:
        Rc = a1 * b1 * c1 / (2 * area2)
        sides = sorted([a1, b1, c1])
        acute = sides[2] ** 2 < sides[0] ** 2 + sides[1] ** 2 + 1e-15
        if acute:
            best = min(best, Rc)
    return best


def objective(params, r, pen=1e3):
    t = params[0::2]
    ph = params[1::2]
    if min(t) < 0 or max(t) + r >= 1 - 1e-9:
        return 1e3 + sum(max(0.0, x + r - (1 - 1e-9)) for x in t)
    g = covering_gap(params, r)          # <=0 required
    pen_v = pen * max(0.0, g) ** 2
    hs = [(t[i] * math.cos(ph[i]), t[i] * math.sin(ph[i])) for i in range(3)]
    return -min_enclosing(hs) + pen_v


def main():
    r = U
    rng = np.random.default_rng(7)
    best = (1e9, None)
    t0 = time.time()
    trials = 0
    while time.time() - t0 < 240 and trials < 4000:
        trials += 1
        p0 = np.concatenate([rng.uniform(0.02, 0.6, 3), rng.uniform(0, 2 * math.pi, 3)])
        res = minimize(objective, p0, args=(r,), method="Nelder-Mead",
                       options=dict(maxfev=4000, xatol=1e-10, fatol=1e-12, adaptive=True))
        if res.fun < best[0]:
            best = (float(res.fun), res.x.copy())
            t = best[1][0::2]
            ph = best[1][1::2]
            hs = [(t[i] * math.cos(ph[i]), t[i] * math.sin(ph[i])) for i in range(3)]
            R = min_enclosing(hs)
            g = covering_gap(best[1], r)
            print("new best: -R+pen=%.6f  R=%.6f  gap=%.3e  t=%s  R-U=%+.5f  (%.0fs, %d)"
                  % (best[0], R, g, np.round(t, 5), R - U, time.time() - t0, trials),
                  flush=True)
    t = best[1][0::2]
    ph = best[1][1::2]
    hs = [(float(t[i] * math.cos(ph[i])), float(t[i] * math.sin(ph[i]))) for i in range(3)]
    out = dict(r=r, best_params=best[1].tolist(), hub_positions=hs,
               min_enclosing_radius=min_enclosing(hs), U=U,
               cover_gap=covering_gap(best[1], r), trials=trials,
               seconds=time.time() - t0,
               interpretation=("gap<=0 means the three arcs cover S(0,a) hence the core; "
                               "R>U with gap<=0 would be a counterexample to the claim"))
    (HERE / "three_hub_probe.json").write_text(json.dumps(out, indent=1))
    print(json.dumps({k: v for k, v in out.items() if k != "best_params"}, indent=1))


if __name__ == "__main__":
    main()
