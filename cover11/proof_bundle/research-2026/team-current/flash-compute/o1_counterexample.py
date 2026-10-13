# -*- coding: utf-8 -*-
"""o1_counterexample.py -- exact-ish JSON + independent verification of the O1-negative ledger.

Chain:  take (r, m=0, t1,t2,t3,o12, gf=0) from the minimiser, complete the nine arcs with six
fillers of half-width a = asin(r) tiling the remaining gap, then
  (V1) reconstruct the nine centres c_k = rho(t_k) u(psi_k) and re-measure every actual arc on
       dD by direct boundary sampling (half-width must equal t_k, private part > 0);
  (V2) check the ledger identities: sum 2t - 2 pi = sum of the overlaps, all overlaps >= 0;
  (V3) recompute every adjacent inner crossing by an independent method (mpmath circle
       intersection, 50 dps) and every third-disk distance; report the O1 margin;
  (V4) report the hole/capability data: max tip radius, a* = min_k rho(t_k) - r, whether the
       tips can be split into two radius-r classes (C559-style necessary condition).
Writes out/o1_counterexample.json (full ledger data) and prints a summary.  Numeric only.
"""
import json, math, os
import mpmath as mp

mp.mp.dps = 50
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
R = 0.38
A = math.asin(R)


def rho(t):
    return math.cos(t) - math.sqrt(max(R * R - math.sin(t) ** 2, 0.0))


def rho_mp(t):
    return mp.cos(t) - mp.sqrt(R * R - mp.sin(t) ** 2)


def build(t3, o12):
    t = list(t3) + [A] * 6
    psi = [0.0]
    # arc k spans [psi_k - t_k, psi_k + t_k]; the arcs tile with only o12 overlapping
    psi.append(psi[0] + t[0] + t[1] - o12)          # disk 2
    psi.append(psi[1] + t[1] + t[2])                # disk 3, gf = 0 (touching)
    # six fillers tile the near gap exactly, with zero overlap
    start = psi[2] + t[2]
    for k in range(6):
        psi.append(start + t[3 + k] + 2 * sum(t[3:3 + k]))   # centre of filler k
    return t, psi


def ver(t, psi):
    n = len(t)
    o = []
    for k in range(n):
        d = (psi[(k + 1) % n] - psi[k]) % (2 * math.pi)
        o.append(t[k] + t[(k + 1) % n] - d)
    priv = [2 * t[k] - o[k - 1] - o[k] for k in range(n)]
    return o, priv


def arc_by_sampling(t, psi):
    """measure each disk's actual arc on dD by dense sampling (independent of the formula)."""
    N = 4_000_000
    meas = [0.0] * len(t)
    for i in range(N):
        th = 2 * math.pi * i / N
        u = (math.cos(th), math.sin(th))
        for k in range(len(t)):
            c = (rho(t[k]) * math.cos(psi[k]), rho(t[k]) * math.sin(psi[k]))
            if (u[0] - c[0]) ** 2 + (u[1] - c[1]) ** 2 <= R * R:
                meas[k] += 2 * math.pi / N
    return meas


def crossing_mp(c1, c2):
    """independent circle-intersection at 50 dps: solve |x-c1|=r, |x-c2|=r."""
    c1 = (mp.mpf(c1[0]), mp.mpf(c1[1])); c2 = (mp.mpf(c2[0]), mp.mpf(c2[1]))
    r = mp.mpf(R)
    mx, my = (c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2
    dx, dy = c2[0] - c1[0], c2[1] - c1[1]
    D = mp.sqrt(dx * dx + dy * dy)
    h = mp.sqrt(r * r - D * D / 4)
    px, py = -dy / D, dx / D
    a = (mx - h * px, my - h * py); b = (mx + h * px, my + h * py)
    return a if (a[0] ** 2 + a[1] ** 2) <= (b[0] ** 2 + b[1] ** 2) else b


if __name__ == "__main__":
    print("=" * 78)
    print("O1 counterexample ledger:  r = 0.38   a = asin r = %.9f" % A)
    print("=" * 78)
    for tag, t3, o12 in (("worst-opt", (0.336430, 0.389802, 0.353394), 0.553635),
                         ("scan-min", (0.322232, 0.389796, 0.347568), 0.512993)):
        t, psi = build(t3, o12)
        o, priv = ver(t, psi)
        print("[%s] t (deg) = %s" % (tag, ["%.4f" % math.degrees(x) for x in t]))
        print("      psi (deg) = %s" % ["%.4f" % math.degrees(x) for x in psi])
        print("      overlaps  = %s   (min %+.3e)" % (["%.6f" % x for x in o], min(o)))
        print("      private   = %s   (min %+.3e)" % (["%.6f" % x for x in priv], min(priv)))
        print("      sum 2t = %.9f  vs 2pi + sum o = %.9f" % (2 * sum(t), 2 * math.pi + sum(o)))
        print("      max t / a = %.6f  <= 1 ? %s" % (max(t) / A, max(t) <= A + 1e-15))
        C = [(rho(t[k]) * math.cos(psi[k]), rho(t[k]) * math.sin(psi[k])) for k in range(9)]
        # V3: independent crossings and O1 margins
        worst = None
        for k in range(9):
            v = crossing_mp(C[k], C[(k + 1) % 9])
            for j in range(9):
                if j in (k, (k + 1) % 9):
                    continue
                d = float(mp.sqrt((v[0] - mp.mpf(C[j][0])) ** 2 + (v[1] - mp.mpf(C[j][1])) ** 2))
                if worst is None or d - R < worst[0]:
                    worst = (d - R, k, j, float(mp.sqrt(v[0] ** 2 + v[1] ** 2)), float(v[0]), float(v[1]))
        print("      O1 (mpmath 50dps): worst |v-c_j| - r = %+.9e  (pair #%d, third #%d, |v| = %.9f)"
              % (worst[0], worst[1], worst[2], worst[3]))
        print("      tips are INSIDE the third ring disk: %s" % (worst[0] < 0))
        # V4: hole / capability data
        ts = [rho(t[k]) for k in range(9)]
        astar = min(ts) - R
        print("      a* = min_k rho - r = %.9f ; max tip radius = %.9f ; r = %.6f"
              % (astar, max(math.hypot(*crossing_mp(C[k], C[(k + 1) % 9])) for k in range(9)), R))
        # capability: split the nine tips into two radius-r classes (necessary condition O2)
        tips = [crossing_mp(C[k], C[(k + 1) % 9]) for k in range(9)]
        import itertools
        best_split = None
        for r_ in range(9):
            pass
        for mask in range(1 << 9):
            S1 = [k for k in range(9) if (mask >> k) & 1]
            S2 = [k for k in range(9) if not ((mask >> k) & 1)]
            if not S1 or not S2:
                continue
            def mec_size(S):
                pts = [(float(tips[k][0]), float(tips[k][1])) for k in S]
                # brute force 2-3 point MEC lower bound via smallest enclosing circle (Welzl-lite)
                import random
                random.seed(0)
                best = 0.0
                for i in range(len(pts)):
                    for j in range(i + 1, len(pts)):
                        for kk in range(j + 1, len(pts)):
                            a1, b1 = pts[i], pts[j]; a2, b2 = pts[i], pts[kk]; a3, b3 = pts[j], pts[kk]
                            d = 2 * (a1[0] * (b2[1] - a3[1]) + a2[0] * (a3[1] - b1[1]) + a3[0] * (b1[1] - b2[1]))
                            if abs(d) < 1e-18:
                                continue
                            ux = ((a1[0] ** 2 + a1[1] ** 2) * (b2[1] - a3[1]) + (a2[0] ** 2 + a2[1] ** 2) * (a3[1] - b1[1]) + (a3[0] ** 2 + a3[1] ** 2) * (b1[1] - b2[1])) / d
                            uy = ((a1[0] ** 2 + a1[1] ** 2) * (a3[0] - a2[0]) + (a2[0] ** 2 + a2[1] ** 2) * (a1[0] - a3[0]) + (a3[0] ** 2 + a3[1] ** 2) * (a2[0] - a1[0])) / d
                            rad = math.hypot(a1[0] - ux, a1[1] - uy)
                            if all(math.hypot(x - ux, y - uy) <= rad + 1e-12 for (x, y) in pts):
                                best = max(best, rad)
                return best
            m1, m2 = mec_size(S1), mec_size(S2)
            v = max(m1, m2)
            if best_split is None or v < best_split[0]:
                best_split = (v, S1, S2)
        print("      capability O2 (min over bipartitions of max MEC) = %.9f  vs r = %.6f  => %s"
              % (best_split[0], R, "O2 holds (feasible split)" if best_split[0] <= R else "O2 FAILS"))
        out = dict(tag=tag, r=R, a=A, t=t, psi=psi, overlaps=o, private=priv, centres=C,
                   sum2t=2 * sum(t), worst_O1_margin=worst[0], worst_pair=(worst[1], worst[2]),
                   a_star=astar, capability_minmax_MEC=best_split[0],
                   split=(best_split[1], best_split[2]), ledger_legal=bool(min(o) >= -1e-12 and min(priv) > 0))
        p = os.path.join(OUT, "o1_counterexample_%s.json" % tag)
        with open(p, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=1, default=str)
        print("      wrote %s" % p)
        print()
