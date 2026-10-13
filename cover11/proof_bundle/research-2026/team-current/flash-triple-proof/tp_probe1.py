# -*- coding: utf-8 -*-
"""tp_probe1.py -- STRUCTURAL PROBE 1 (named obligation, bounded <= 10 min).

Obligation: locate the worst case of the hole-depth functional
      G(object) = max_{z in D} min_i |z - c_i|
over the triple-common-point subclass (nine boundary disks), and record WHICH constraint
binds at the optimum.  Decision it can change: whether the 3-point-packing mechanism
(pairwise > 2r) or the empty-disk mechanism (> r) is the right proof target, and whether
both are hopeless (which would redirect to the hub-cover route).

Stop condition: stop this experiment at 10 min wall clock OR when 40000 legal objects have
been evaluated OR on the first object with pairwise-3-packing feasibility; the deliverable is
the argmin object plus the binding-constraint pattern, not a certificate.

Construction of each object:
  cluster: three centres inside B(p,r) (hence min_x max_i |x-c_i| <= r automatically),
           their arcs consecutive and of union span S <= 2 asin(2r);
  outer six: inward-root centres c_j = c(t_j, psi_j) on the complement of the cluster arc,
           t_j = A - delta_j with sum delta_j <= Dmax, t_j >= t0;
  legality: arc overlaps >= 0 (cyclic), private widths > 0.
"""
import json
import math
import os
import random
import time
import numpy as np

import tp_geom as G

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
R, A, B = G.R, G.A, G.B
T0, RHO0, DMAX, S_MAX = G.T0, G.RHO0, G.DMAX, G.S_MAX
T0MIN = T0          # lower bound on outer half-widths


def cluster_centres(p, angles, radii):
    return [(p[0] + radii[i] * math.cos(angles[i]), p[1] + radii[i] * math.sin(angles[i]))
            for i in range(3)]


def build(p_dist, cluster_ang, cluster_rad, deltas, ov_extra, start_mode):
    """Return (C, info) with 9 centres in cyclic order: cluster 0,1,2 then outer 3..8."""
    thp = 0.0
    p = (p_dist, 0.0)
    C3 = cluster_centres(p, cluster_ang, cluster_rad)
    # cluster arcs (actual)
    t3 = [G.arc_halfwidth(math.hypot(*c)) for c in C3]
    ph3 = [math.atan2(c[1], c[0]) for c in C3]
    order = sorted(range(3), key=lambda i: ph3[i])
    t3 = [t3[i] for i in order]; ph3 = [ph3[i] for i in order]; C3 = [C3[i] for i in order]
    a0, b0 = ph3[0] - t3[0], ph3[0] + t3[0]
    for k in range(1, 3):
        a, b = ph3[k] - t3[k], ph3[k] + t3[k]
        if a > b0 + 1e-9:
            return None
        b0 = max(b0, b)
    S = b0 - a0
    if S > S_MAX + 1e-9 or min(t3) <= 1e-9:
        return None
    if sum(deltas) > DMAX + 1e-12:
        return None
    t6 = [A - d for d in deltas]
    if min(t6) < T0MIN - 1e-12:
        return None
    span = 2 * math.pi - S                       # angle left for the six arcs
    if 2 * sum(t6) + ov_extra < span - 1e-9:
        return None
    ov = (2 * sum(t6) - span) / 5.0 + ov_extra / 5.0    # equal overlap redistribution
    if ov < -1e-12:
        return None
    C6 = []
    cur = b0
    for k in range(6):
        C6.append(G.centre_of(t6[k], cur + t6[k]))
        cur += 2 * t6[k] - ov
    C = C3 + C6
    info = dict(p=p, t3=t3, t6=t6, S=S, deltas=list(deltas), ov=ov)
    return C, info


def legality(C, info):
    """arc ledger legality in cyclic order cluster(0,1,2) then 3..8."""
    led = G.ledger(C, cluster_idx=(0, 1, 2))
    t = led["t"]
    return (min(led["o"]) > -1e-9 and min(led["priv"]) > 1e-9 and min(t) > 1e-9,
            led)


def main():
    t_start = time.time()
    rng = random.Random(20260924)
    rows = []
    tried = 0
    stop = "budget/count"
    limit_s = 600.0
    while time.time() - t_start < limit_s:
        tried += 1
        p_dist = rng.uniform(0.0, 1 - 2 * R + 1e-9)
        cluster_ang = [rng.uniform(0, 2 * math.pi) for _ in range(3)]
        cluster_rad = [rng.uniform(0.5 * R, R) for _ in range(3)]
        mode = rng.random()
        D = DMAX * rng.uniform(0.85, 1.0)
        if mode < 0.35:
            deltas = [D / 6] * 6
        elif mode < 0.55:
            deltas = [D, 0, 0, 0, 0, 0]
        elif mode < 0.75:
            deltas = [D / 2, D / 2, 0, 0, 0, 0]
        else:
            w = [rng.random() for _ in range(6)]
            sw = sum(w)
            deltas = [x / sw * D for x in w]
        out = build(p_dist, cluster_ang, cluster_rad, deltas, 0.0, 0)
        if out is None:
            continue
        C, info = out
        ok, led = legality(C, info)
        if not ok:
            continue
        g, z = G.deep_point(C, ngrid=60)
        rows.append((g, z, C, info, led))
        if len(rows) >= 4000:
            stop = "count cap"
            break
    rows.sort(key=lambda t: t[0])
    print("=" * 78)
    print("probe1: hole-depth G over the triple-common-point subclass   (r = %.4f)" % R)
    print("stop: %s ; legal objects: %d (from %d tries) ; wall %.1fs"
          % (stop, len(rows), tried, time.time() - t_start))
    if not rows:
        print("no legal object found -- construction or domain is wrong")
        return
    gs = np.array([x[0] for x in rows])
    for q in (0, 1, 5, 25, 50, 75, 95, 100):
        print("   G  q%3d%% = %.6f" % (q, float(np.percentile(gs, q))))
    print("   G/r : min %.6f   max %.6f" % (gs.min() / R, gs.max() / R))
    worst = rows[0]
    print("WORST: G = %.9f  (G/r = %.6f, G-2r = %+.6f)  at z = (%.6f, %.6f)"
          % (worst[0], worst[0] / R, worst[0] - 2 * R, worst[1][0], worst[1][1]))
    print("   |p| = %.6f ; S = %.6f (bound %.6f) ; t3(deg) = %s ; t6(deg) = %s"
          % (math.hypot(*worst[3]["p"]), worst[3]["S"], S_MAX,
             ["%.3f" % math.degrees(x) for x in worst[3]["t3"]],
             ["%.3f" % math.degrees(x) for x in worst[3]["t6"]]))
    print("   deficit = %.6f (bound %.6f) ; overlap = %.3e ; min private = %.6f"
          % (sum(worst[3]["deltas"]), DMAX, min(worst[4]["o"]), min(worst[4]["priv"])))
    n3 = sum(1 for x in rows if x[0] > 2 * R)
    print("   objects with G > 2r (empty disk radius > r): %d / %d" % (n3, len(rows)))
    # for the worst, report the 3-packing status
    k, pts = G.sep3_packing(worst[2])
    print("   worst-object 3-packing: k = %d (points %s)" % (k, [tuple(round(v, 5) for v in q) for q in pts]))
    with open(os.path.join(OUT, "tp_probe1.json"), "w", encoding="utf-8") as f:
        json.dump(dict(r=R, stop=stop, n=len(rows), tried=tried,
                       G_quantiles={str(q): float(np.percentile(gs, q)) for q in (0, 1, 5, 25, 50, 100)},
                       worst=dict(G=float(worst[0]), z=[float(v) for v in worst[1]],
                                  p=[float(v) for v in worst[3]["p"]],
                                  S=float(worst[3]["S"]),
                                  t3=[float(v) for v in worst[3]["t3"]],
                                  t6=[float(v) for v in worst[3]["t6"]],
                                  deficit=float(sum(worst[3]["deltas"])),
                                  centres=[[float(a), float(b)] for a, b in worst[2]])),
            f, indent=1)
    print("wrote out/tp_probe1.json")


if __name__ == "__main__":
    main()
