# -*- coding: utf-8 -*-
"""tp_probe3.py -- STRUCTURAL PROBE 3 (named obligation, <= 10 min, backgrounded).

Obligation: for the q=1 subclass (three consecutive ring disks sharing a common point p,
six outer ring disks, arcs essential/consecutive with first-order overlap only, deficits
sum_j (A - t_j) <= Dmax), decide numerically whether the hole H = D \\ union_9 can always be
covered by two radius-r disks whose centres lie in the hub feasible region
      C = {h : |h| >= rhoC, h within reach of the core circle |w| = rhoC},
      rhoC = rho(t) at t = A - Dmax  (numerically ~ 0.7467),
and locate the extremal object + the binding constraint.

Model of each object (all parameters named):
  p            = cluster common point, |p| = P, angle 0 (rotational frame),
  cluster      : three centres c_k = rho_k * (p/|p| rotated by theta_k) reached from p:
                 direction from p = pi + theta_k, distance rho_k <= r   (so p is common),
  outer six    : half-widths t_j = A - delta_j with sum delta_j <= Dmax (uniform/one/two/rand),
                 centres = inward-root positions tiling the complement of the cluster union arc,
  hubs         : h1 = +a*u, h2 = -a*u for u = e^{i psi}, a in [rhoC - r, rhoC + r] restricted
                 to the feasible window.
Search: randomized + local refinement over (P, theta_k, rho_k, delta mode, psi, a) to MINIMIZE
the margin  G(object) - r  where G = max_{z in D} min_i |z - c_i|  (the deepest hole point's
distance to the nine ring centres).  G > r is necessary for a 3-packing witness and is our
target quantity.

Stop condition: <= 600 s wall clock OR 3000 legal objects OR first object with G <= r.
Deliverable (numeric only): the extremal object, G_min, G_min/r and the binding pattern.
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


def build_outer(b0, span, t6, mode_deltas):
    n = len(t6)
    tot = 2 * sum(t6)
    ov = (tot - span) / (n - 1) if tot > span else 0.0
    C = []
    cur = b0
    for k in range(n):
        C.append(G.centre_of(t6[k], cur + t6[k]))
        cur += 2 * t6[k] - ov
    return C


def cluster_block(P, p_ang, thetas, rhos):
    p = (P * math.cos(p_ang), P * math.sin(p_ang))
    C3 = []
    for k in range(3):
        th = p_ang + math.pi + thetas[k]
        C3.append((p[0] + rhos[k] * math.cos(th), p[1] + rhos[k] * math.sin(th)))
    t3 = [G.arc_halfwidth(math.hypot(*c)) for c in C3]
    if min(t3) <= 1e-9:
        return None
    ph3 = [math.atan2(c[1], c[0]) for c in C3]
    bands = sorted((ph3[k] - t3[k], ph3[k] + t3[k]) for k in range(3))
    merged = [list(bands[0])]
    for a, b in bands[1:]:
        if a <= merged[-1][1] + 1e-9:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    if len(merged) == 2 and (merged[1][1] - 2 * math.pi) <= merged[0][0] + 1e-9:
        b0 = merged[0][1]
        S = merged[0][1] - (merged[1][0] - 2 * math.pi)
    elif len(merged) == 1:
        b0 = merged[0][1]
        S = merged[0][1] - merged[0][0]
    else:
        return None
    if S > S_MAX + 1e-9:
        return None
    return C3, t3, S, b0


def G_of(C):
    n = len(C)
    best = -1.0
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
                if dd > best:
                    best = dd
    # boundary candidates: antipodes and equal-min crossings
    N = 720
    th = 2 * math.pi * np.arange(N) / N
    X = np.cos(th); Y = np.sin(th)
    D = np.full(N, 1e9)
    for (cx, cy) in C:
        D = np.minimum(D, np.hypot(X - cx, Y - cy))
    i = int(np.argmax(D))
    if D[i] > best:
        best = float(D[i])
    return best


def polish(C, z, step=0.05):
    f = lambda w: G.dmin(C, w)
    b = f(z)
    s = step
    for _ in range(120):
        imp = False
        for dx, dy in ((s, 0), (-s, 0), (0, s), (0, -s)):
            w = (z[0] + dx, z[1] + dy)
            if math.hypot(*w) > 1.0:
                continue
            v = f(w)
            if v > b + 1e-15:
                b, z, imp = v, w, True
        if not imp:
            s *= 0.5
            if s < 1e-11:
                break
    return b, z


def evaluate(P, p_ang, thetas, rhos, deltas):
    out = cluster_block(P, p_ang, thetas, rhos)
    if out is None:
        return None
    C3, t3, S, b0 = out
    t6 = [A - d for d in deltas]
    if min(t6) < T0 - 1e-12 or sum(deltas) > DMAX + 1e-12:
        return None
    span = 2 * math.pi - S
    if 2 * sum(t6) < span - 1e-9:
        return None
    C6 = build_outer(b0, span, t6, deltas)
    C = C3 + C6
    led = G.ledger(C, cluster_idx=(0, 1, 2))
    if min(led["o"]) < -1e-8 or min(led["priv"]) < 1e-9:
        return None
    return C, dict(t3=t3, t6=t6, S=S, deltas=deltas, o=led["o"], priv=led["priv"])


def main():
    t0 = time.time()
    rng = np.random.default_rng(2026)
    rows = []
    tries = 0
    stop = "budget"
    while time.time() - t0 < 600:
        tries += 1
        P = float(rng.uniform(0.30, 1 - 2 * R))
        # the three actual arcs must form ONE consecutive block of width <= 2 asin(2r):
        # the centre directions from O must lie in a window of half-width (B + A) around p's
        # direction; |dir from p to c_k| <= asin(r/|p|).  Sample thetas inside that window.
        win = max(B + A - P, 0.0)
        win = min(win, 1.3)
        p_ang = 0.0
        thetas = [float(rng.uniform(-win, win)) for _ in range(3)]
        rhos = [float(rng.uniform(0.82 * R, R)) for _ in range(3)]
        u = rng.random()
        D = DMAX * float(rng.uniform(0.9, 1.0))
        if u < 0.4:
            deltas = [D / 6] * 6
        elif u < 0.6:
            deltas = [D, 0, 0, 0, 0, 0]
        elif u < 0.8:
            deltas = [D / 2, D / 2, 0, 0, 0, 0]
        else:
            w = rng.random(6); deltas = list(w / w.sum() * D)
        ev = evaluate(P, p_ang, thetas, rhos, deltas)
        if ev is None:
            continue
        C, info = ev
        # candidate seeds: grid + Voronoi vertices (G_of returns only the value, recompute seeds)
        g = G_of(C)
        seeds = [(0.0, 0.0)]
        n = len(C)
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
                    if ux * ux + uy * uy <= 1.0:
                        seeds.append((ux, uy))
        for i in range(n):
            for j in range(i + 1, n):
                x0, y0 = C[i]; x1, y1 = C[j]
                mx, my = (x0 + x1) / 2, (y0 + y1) / 2
                a1 = x1 - x0; b1 = y1 - y0
                for t in (-1.0, 1.0):
                    px, py = mx - b1 * t * 0.5, my + a1 * t * 0.5
                    if px * px + py * py <= 1.0:
                        seeds.append((px, py))
        gbest = -1.0; zbest = None
        for s in seeds[:60]:
            v, zz = polish(C, s, step=0.03)
            if v > gbest:
                gbest, zbest = v, zz
        g, z = gbest, zbest
        rows.append((g, z, C, info))
        if g <= R:
            stop = "FOUND G<=r"
            break
        if len(rows) >= 3000:
            stop = "count cap"
            break
    rows.sort(key=lambda t: t[0])
    gs = np.array([x[0] for x in rows]) if rows else np.array([0.0])
    print("=" * 78)
    print("probe3: G = deepest hole depth over q=1 subclass ; r = %.4f" % R)
    print("stop %s ; legal %d / tries %d ; wall %.1fs" % (stop, len(rows), tries, time.time() - t0))
    for q in (0, 1, 5, 25, 50, 100):
        print("   G q%3d%% = %.6f   G/r = %.6f" % (q, float(np.percentile(gs, q)),
                                                    float(np.percentile(gs, q)) / R))
    if rows:
        w = rows[0]
        P = w[2]
        ds = sorted((math.dist(w[1], c), i) for i, c in enumerate(P))
        print("WORST G = %.9f at z* = (%.5f, %.5f) |z*| = %.6f" % (w[0], w[1][0], w[1][1], math.hypot(*w[1])))
        print("   nearest: " + " ".join("c%d %.5f" % (i, d) for d, i in ds[:4]))
        print("   |c_i| = " + " ".join("%.4f" % math.hypot(*c) for c in P))
        print("   t3(deg) = %s t6(deg) = %s S = %.5f deficit = %.6f"
              % (["%.3f" % math.degrees(x) for x in w[3]["t3"]],
                 ["%.3f" % math.degrees(x) for x in w[3]["t6"]], w[3]["S"], sum(w[3]["deltas"])))
        json.dump(dict(r=R, stop=stop, n=len(rows), tries=tries,
                       G_min=float(gs.min()), G_over_r=float(gs.min() / R),
                       worst=dict(G=float(w[0]), z=[float(v) for v in w[1]],
                                  centres=[[float(a), float(b)] for a, b in P],
                                  t3=[float(v) for v in w[3]["t3"]],
                                  t6=[float(v) for v in w[3]["t6"]],
                                  S=float(w[3]["S"]), deficit=float(sum(w[3]["deltas"]))),
                       quantiles={str(q): float(np.percentile(gs, q)) for q in (0, 1, 5, 50, 100)}),
                  open(os.path.join(OUT, "tp_probe3.json"), "w", encoding="utf-8"), indent=1)
        print("wrote out/tp_probe3.json")


if __name__ == "__main__":
    main()
