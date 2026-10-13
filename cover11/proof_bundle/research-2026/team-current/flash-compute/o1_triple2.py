# -*- coding: utf-8 -*-
"""o1_triple2.py -- O1 three-disk domain: feasible sampling + minimisation + completion.

Domain (necessary conditions of a legal 9-arc ledger, r fixed, a = asin r):
  t1,t2,t3 in (0,a];  o12 in [0, 2 min(t1,t2))] (adjacent pair overlap with private parts);
  signed far gap gf (= psi3 - psi2 - t2 - t3) and near gap
      gn = 2 pi - (psi3-psi1) - t1 - t3 = 2 pi - 2(t1+t2+t3) + o12 - gf
  with, by the coverage budgets (each of the other arcs has half-width <= a):
      m = 0 (disk j adjacent to the pair, overlap o23 = -gf):
            gf in [-2min(t2,t3), 0],        gn in [0, 12a]
      1 <= m <= 5:
            gf in [0, 2ma],                 gn in [0, 2(6-m)a]
      m = 6 (disk j adjacent to disk 1, overlap o31 = -gn):
            gf in [0, 12a],                 gn in [-2min(t1,t3), 0]
  margin  mu = |v12 - c3| - r      (v12 = inner crossing of disks 1,2)
  scalar  sc = rho3 |sin(delta)| - r,  delta = angle(v12) - angle(c3)
             (structure C784 style sufficient condition; NOT equivalent to mu)

PART 1: multistart SLSQP over (t1,t2,t3,o12,gf) per m.
PART 2: explicit completion of the worst triple to a legal 9-ring (fillers of half-width
        t = max(G/(2m), eps) placed consecutively), full legality check, direct O1 test,
        and a JSON dump of the worst legal ledger.
Numeric only.
"""
import json
import math
import os
import numpy as np
from scipy.optimize import minimize

S = 10 ** 17
ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")


def rho(t, r):
    return math.cos(t) - math.sqrt(max(r * r - math.sin(t) ** 2, 0.0))


def centre(t, psi, r):
    rr = rho(t, r)
    return (rr * math.cos(psi), rr * math.sin(psi))


def crossings(c1, c2, r):
    dx, dy = c2[0] - c1[0], c2[1] - c1[1]
    D = math.hypot(dx, dy)
    h = math.sqrt(max(r * r - D * D / 4, 0.0))
    mx, my = (c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2
    px, py = -dy / D, dx / D
    a = (mx - h * px, my - h * py)
    b = (mx + h * px, my + h * py)
    return (a, b) if a[0] ** 2 + a[1] ** 2 <= b[0] ** 2 + b[1] ** 2 else (b, a)


def triple_state(x, r, m):
    t1, t2, t3, o12, gf = x
    d12 = t1 + t2 - o12
    psi1, psi2 = 0.0, d12
    psi3 = psi2 + t2 + gf + t3
    c1 = centre(t1, psi1, r); c2 = centre(t2, psi2, r); c3 = centre(t3, psi3, r)
    v = crossings(c1, c2, r)[0]
    gn = 2 * math.pi - (psi3 - psi1) - t1 - t3
    mu = math.dist(v, c3) - r
    angv = math.atan2(v[1], v[0]); ang3 = math.atan2(c3[1], c3[0])
    dlt = abs((angv - ang3 + math.pi) % (2 * math.pi) - math.pi)
    sc = rho(t3, r) * abs(math.sin(dlt)) - r
    return mu, sc, gn, (t1, t2, t3, o12, gf, d12, psi3, v, c3, dlt)


def gf_window(t1, t2, t3, o12, r, m):
    """feasible closed interval for the signed far gap gf."""
    a = math.asin(r)
    S3 = t1 + t2 + t3
    if m == 0:
        lo = max(-(2 * min(t2, t3)), 2 * math.pi - 2 * S3 + o12 - 12 * a)
        hi = 0.0
    elif m == 6:
        lo = 2 * math.pi - 2 * S3 + o12
        hi = min(12 * a, lo + 2 * min(t1, t3))
    else:
        lo = max(0.0, 2 * math.pi - 2 * S3 + o12 - 2 * (6 - m) * a)
        hi = min(2 * m * a, 2 * math.pi - 2 * S3 + o12)
    return lo, hi


def part1(r, m, nstart=250, seed=0):
    a = math.asin(r)
    rng = np.random.default_rng(seed)
    best = None
    for _ in range(nstart):
        t = rng.uniform(0.35 * a, a, 3)
        o = rng.uniform(0, 2 * min(t[0], t[1]) * 0.98)
        lo, hi = gf_window(t[0], t[1], t[2], o, r, m)
        if lo > hi:
            continue
        gf = rng.uniform(lo, hi)
        x0 = np.array([t[0], t[1], t[2], o, gf])
        bnds = [(1e-7, a), (1e-7, a), (1e-7, a),
                (0.0, 2 * min(x0[0], x0[1]) - 1e-9), (None, None)]
        cons = [{"type": "ineq",
                 "fun": lambda x: x[4] - gf_window(x[0], x[1], x[2], x[3], r, m)[0]},
                {"type": "ineq",
                 "fun": lambda x: gf_window(x[0], x[1], x[2], x[3], r, m)[1] - x[4]}]
        res = minimize(lambda x: triple_state(x, r, m)[0], x0, bounds=bnds, constraints=cons,
                       method="SLSQP", options=dict(maxiter=400, ftol=1e-16))
        x = res.x
        lo, hi = gf_window(x[0], x[1], x[2], x[3], r, m)
        if not (lo - 1e-12 <= x[4] <= hi + 1e-12):
            continue
        mu, sc, gn, info = triple_state(x, r, m)
        if best is None or mu < best[0]:
            best = (mu, sc, list(x), m, gn)
    return best


def fill_gap(L, R, m, a):
    """m arcs (half-width <= a) covering [L,R] consecutively with overlaps >= 0 and
       private parts > 0; returns list of (centre, halfwidth)."""
    out = []
    if m <= 0:
        return out
    G = R - L
    t = max(G / (2 * m), 1e-6)
    t = min(t, a)
    if m == 1:
        out.append((0.5 * (L + R), min(t, a)))
        return out
    if G >= 2 * t:
        step = (G - 2 * t) / (m - 1)
    else:
        step = 0.0
    for k in range(m):
        out.append((L + t + step * k, t))
    return out


def complete(x, r, m, tag):
    a = math.asin(r)
    t1, t2, t3, o12, gf = x
    d12 = t1 + t2 - o12
    psi1, psi2 = 0.0, d12
    psi3 = psi2 + t2 + gf + t3
    arcs = [(psi1, t1), (psi2, t2), (psi3, t3)]
    # far gap [arc2 end, arc3 start] gets m fillers (ring order: disks 3..j-1)
    L1, R1 = psi2 + t2, psi3 - t3
    if m > 0 and R1 > L1:
        arcs += fill_gap(L1, R1, m, a)
    elif m > 0:
        # gap degenerate/negative (can happen with gf < 0 only for m=0); place near each other
        for k in range(m):
            arcs.append((0.5 * (L1 + R1), min(a, max(1e-6, abs(R1 - L1) / 2)) if R1 > L1 else 1e-3))
    # near gap [arc3 end, arc1 start + 2pi] gets 6-m fillers
    L2, R2 = psi3 + t3, 2 * math.pi - t1
    mm = 6 - m
    if mm > 0:
        arcs += fill_gap(L2, R2, mm, a)
    order = sorted(range(len(arcs)), key=lambda i: arcs[i][0])
    psi = [arcs[i][0] for i in order]
    tt = [arcs[i][1] for i in order]
    n = len(psi)
    if n != 9:
        return None
    o = []
    for k in range(n):
        d = (psi[(k + 1) % n] - psi[k]) % (2 * math.pi)
        o.append(tt[k] + tt[(k + 1) % n] - d)
    minpriv = min(2 * tt[k] - o[k - 1] - o[k] for k in range(n))
    C = [centre(tt[k], psi[k], r) for k in range(n)]
    # direct O1 over all adjacent pairs and all third ring disks
    worst = None; worst_pair = None
    for k in range(n):
        v = crossings(C[k], C[(k + 1) % n], r)[0]
        for j in range(n):
            if j in (k, (k + 1) % n):
                continue
            mu = math.dist(v, C[j]) - r
            if worst is None or mu < worst:
                worst = mu; worst_pair = (k, j)
    res = dict(tag=tag, r=r, m=m, psi=psi, t=tt, o=o, C=C, min_private=minpriv,
               sum2t=2 * sum(tt), worst_margin=worst, worst_pair=worst_pair,
               ledger_ok=(min(o) >= -1e-9 and minpriv > 0))
    return res


if __name__ == "__main__":
    print("=" * 78)
    print("O1 three-disk domain: minimisation + completion (numeric)")
    print("=" * 78)
    best_global = None
    for r in (0.38, 0.376, 0.3710):
        print("--- r = %.5f   a = %.6f" % (r, math.asin(r)))
        for m in range(7):
            b = part1(r, m)
            if b is None:
                print("    m=%d : no feasible start" % m)
                continue
            print("    m=%d  min mu = %+.6e   scalar(sc) = %+.6e   gn = %+.6f   "
                  "t(deg) = (%.3f, %.3f, %.3f)  o12 = %.6f  gf = %.6f"
                  % (m, b[0], b[1], b[4], *[math.degrees(v) for v in b[2][:3]], b[2][3], b[2][4]))
            if best_global is None or b[0] < best_global[0]:
                best_global = (b[0], r, m, b)
    print()
    print("=" * 78)
    print("worst triple over the scanned domain: mu = %+.6e at r=%.5f, m=%d" % (best_global[0], best_global[1], best_global[2]))
    print("=" * 78)
    mu, r, m, b = best_global
    comp = complete(b[2], r, m, "worst")
    if comp is None:
        print("  completion failed (naive filler placement)")
    else:
        print("  completed ledger: sum 2t = %.9f  (2pi = %.9f)  min o = %+.3e  min private = %+.3e  ok=%s"
              % (comp["sum2t"], 2 * math.pi, min(comp["o"]), comp["min_private"], comp["ledger_ok"]))
        print("  direct O1 on the completed legal 9-ring: worst margin = %+.6e (pair,third = %s)"
              % (comp["worst_margin"], comp["worst_pair"]))
        path = os.path.join(OUT, "o1_worst_ledger.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(dict(tag=comp["tag"], r=comp["r"], m=comp["m"], t=comp["t"], psi=comp["psi"],
                           overlaps=comp["o"], centres=comp["C"], sum2t=comp["sum2t"],
                           min_private=comp["min_private"], worst_margin=comp["worst_margin"],
                           worst_pair=comp["worst_pair"], ledger_ok=comp["ledger_ok"],
                           note="numeric exploration; t/psi in radians; centres from rho(t)"), f, indent=1)
        print("  wrote %s" % path)
