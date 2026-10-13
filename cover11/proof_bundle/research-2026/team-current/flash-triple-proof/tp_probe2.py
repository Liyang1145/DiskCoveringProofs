# -*- coding: utf-8 -*-
"""tp_probe2.py -- STRUCTURAL PROBE 2 (named obligation, <= 10 min, backgrounded).

Obligation (updated by lead 2026-09-24): q=1 is the ONLY live refined-ear class.  So the
sweep is restricted to ONE triple cluster (three consecutive ring disks sharing a point p)
plus six outer ring disks.  Locate the minimum of the hole-depth functional
      G = max_{z in D} min_i |z - c_i|
and the binding-constraint pattern at the optimum (which disk is nearest at z*, where z*
sits relative to the cluster direction, how big G/r is, whether the 3-packing witness
exists).  Decision it can change: proof target (empty disk > r, 3-packing pairwise > 2r,
or hub-reach lemma) and which configuration is extremal.

Stop condition: <= 600 s wall clock, or 1500 legal objects, or the first object with G <= r.
Deliverable = argmin object + binding pattern (numeric only; no certification).
"""
import json
import math
import os
import time
import numpy as np

import tp_geom as G

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
R, A, B = G.R, G.A, G.B
T0, RHO0, DMAX, S_MAX = G.T0, G.RHO0, G.DMAX, G.S_MAX


def build(p_dist, p_ang, cluster_rad, cluster_off, deltas):
    """cluster centres = p + rho_k * e^{i(pi + off_k)} (directions relative to p's radial frame);
    p = p_dist * e^{i p_ang}; outer six tile the complement of the cluster union arc."""
    p = (p_dist * math.cos(p_ang), p_dist * math.sin(p_ang))
    C3 = []
    for k in range(3):
        th = p_ang + math.pi + cluster_off[k]
        C3.append((p[0] + cluster_rad[k] * math.cos(th), p[1] + cluster_rad[k] * math.sin(th)))
    t3 = [G.arc_halfwidth(math.hypot(*c)) for c in C3]
    if min(t3) <= 1e-9:
        return None
    ph3 = [math.atan2(c[1], c[0]) for c in C3]
    bands = []
    for k in range(3):
        bands.append((ph3[k] - t3[k], ph3[k] + t3[k]))
    # merge bands cyclically: find whether they form one consecutive block
    bands.sort()
    merged = [list(bands[0])]
    for a, b in bands[1:]:
        if a <= merged[-1][1] + 1e-9:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    if len(merged) == 2 and (merged[1][1] - 2 * math.pi) <= merged[0][0] + 1e-9:
        tail = merged.pop()
        merged[0][0] += 0  # rotate: block is tail + head
        S = (tail[1] - 2 * math.pi) - merged[0][0] + (tail[0] - merged[0][1]) * 0
        # recompute properly: block = [tail[0]-2pi, merged[0][1]]
        S = merged[0][1] - (tail[0] - 2 * math.pi)
        b0 = merged[0][1]
    elif len(merged) == 1:
        S = merged[0][1] - merged[0][0]
        b0 = merged[0][1]
    else:
        return None
    if S > S_MAX + 1e-9:
        return None
    t6 = [A - d for d in deltas]
    if min(t6) < T0 - 1e-12 or sum(deltas) > DMAX + 1e-12:
        return None
    span = 2 * math.pi - S
    if 2 * sum(t6) < span - 1e-9:
        return None
    ov = (2 * sum(t6) - span) / 5.0
    C6 = []
    cur = b0
    for k in range(6):
        C6.append(G.centre_of(t6[k], cur + t6[k]))
        cur += 2 * t6[k] - ov
    C = C3 + C6
    info = dict(p=p, t3=t3, t6=t6, S=S, deltas=list(deltas), ov=ov)
    return C, info


def deep_fast(C):
    """maximize min_i |z-c_i| over D: interior Voronoi vertices (triples) + boundary scan."""
    n = len(C)
    best = (-1.0, (0.0, 0.0))
    P = np.array(C)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                ax, ay = C[i]; bx, by = C[j]; cx, cy = C[k]
                d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
                if abs(d) < 1e-14:
                    continue
                ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay)
                      + (cx * cx + cy * cy) * (ay - by)) / d
                uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx)
                      + (cx * cx + cy * cy) * (bx - ax)) / d
                if ux * ux + uy * uy > 1.0:
                    continue
                dd = float(np.min(np.hypot(P[:, 0] - ux, P[:, 1] - uy)))
                if dd > best[0]:
                    best = (dd, (ux, uy))
    N = 1440
    th = 2 * math.pi * np.arange(N) / N
    X = np.cos(th); Y = np.sin(th)
    D = np.full(N, 1e9)
    for (cx, cy) in C:
        D = np.minimum(D, np.hypot(X - cx, Y - cy))
    i = int(np.argmax(D))
    if D[i] > best[0]:
        best = (float(D[i]), (float(X[i]), float(Y[i])))
    return G.polish(C, best[1], step=0.02)


def main():
    t0 = time.time()
    rng = np.random.default_rng(7)
    rows = []
    tries = 0
    stop = "budget"
    while time.time() - t0 < 600:
        tries += 1
        p_dist = float(rng.uniform(0.0, 1 - 2 * R))
        p_ang = float(rng.uniform(0, 2 * math.pi))
        cluster_rad = [float(rng.uniform(0.55 * R, R)) for _ in range(3)]
        cluster_off = [float(rng.uniform(-1.2, 1.2)) for _ in range(3)]
        u = rng.random()
        D = DMAX * float(rng.uniform(0.85, 1.0))
        if u < 0.35:
            deltas = [D / 6] * 6
        elif u < 0.55:
            deltas = [D, 0, 0, 0, 0, 0]
        elif u < 0.75:
            deltas = [D / 2, D / 2, 0, 0, 0, 0]
        else:
            w = rng.random(6); deltas = list(w / w.sum() * D)
        out = build(p_dist, p_ang, cluster_rad, cluster_off, deltas)
        if out is None:
            continue
        C, info = out
        led = G.ledger(C, cluster_idx=(0, 1, 2))
        if min(led["o"]) < -1e-9 or min(led["priv"]) < 1e-9:
            continue
        g, z = deep_fast(C)
        rows.append((g, z, C, info, led))
        if g <= R:
            stop = "FOUND G<=r"
            break
        if len(rows) >= 1500:
            stop = "count cap"
            break
    rows.sort(key=lambda t: t[0])
    gs = np.array([x[0] for x in rows])
    print("=" * 78)
    print("probe2: hole depth over single-triple (q=1) subclass ; r=%.4f ; stop=%s" % (R, stop))
    print("legal objects %d from %d tries ; wall %.1fs" % (len(rows), tries, time.time() - t0))
    for q in (0, 1, 5, 25, 50, 100):
        print("   G q%3d%% = %.6f   (G/r = %.6f)" % (q, float(np.percentile(gs, q)),
                                                      float(np.percentile(gs, q)) / R))
    w = rows[0]
    P = w[2]
    print("WORST: G = %.9f (G-2r = %+.6f)  z* = (%.6f,%.6f) |z*| = %.6f" %
          (w[0], w[0] - 2 * R, w[1][0], w[1][1], math.hypot(*w[1])))
    print("   |p| = %.6f  p = (%.6f,%.6f) ; S = %.6f ; t3(deg) = %s ; t6(deg) = %s" %
          (math.hypot(*w[3]["p"]), w[3]["p"][0], w[3]["p"][1], w[3]["S"],
           ["%.3f" % math.degrees(x) for x in w[3]["t3"]],
           ["%.3f" % math.degrees(x) for x in w[3]["t6"]]))
    print("   deficit = %.6f ; overlaps min %.3e ; private min %.6f" %
          (sum(w[3]["deltas"]), min(w[4]["o"]), min(w[4]["priv"])))
    ds = [(i, math.dist(w[1], c)) for i, c in enumerate(P)]
    ds.sort(key=lambda t: t[1])
    print("   nearest centres at z*: " + " , ".join("c%d %.6f" % (i, d) for i, d in ds[:4]))
    print("   radial distances |c_i|: " + " ".join("%.4f" % math.hypot(*c) for c in P))
    ang = np.degrees(np.arctan2(w[1][1], w[1][0]))
    print("   angle(z*) = %.2f deg ; angle(p) = %.2f deg ; difference %.2f deg"
          % (ang, math.degrees(math.atan2(w[3]["p"][1], w[3]["p"][0])),
             (ang - math.degrees(math.atan2(w[3]["p"][1], w[3]["p"][0]))) % 360))
    with open(os.path.join(OUT, "tp_probe2.json"), "w", encoding="utf-8") as f:
        json.dump(dict(r=R, stop=stop, n=len(rows), tries=tries,
                       G_min=float(gs.min()), G_q={str(q): float(np.percentile(gs, q)) for q in (0, 1, 5, 50, 100)},
                       worst=dict(G=float(w[0]), z=[float(v) for v in w[1]], p=[float(v) for v in w[3]["p"]],
                                  S=float(w[3]["S"]), t3=[float(v) for v in w[3]["t3"]],
                                  t6=[float(v) for v in w[3]["t6"]],
                                  deficit=float(sum(w[3]["deltas"])),
                                  centres=[[float(a), float(b)] for a, b in P])), f, indent=1)
    print("wrote out/tp_probe2.json")


if __name__ == "__main__":
    main()
