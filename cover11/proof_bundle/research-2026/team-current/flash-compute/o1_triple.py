# -*- coding: utf-8 -*-
"""o1_triple.py -- independent attack on O1 (flash-structure NEXT-OBLIGATION §4), numeric.

O1: for every legal 17D ledger (nine radius-r disks covering the unit circle, actual arcs
t_1..t_9, half-widths <= asin r, cyclic order) and every adjacent pair (i,i+1), the inner
crossing v_i of their boundary circles is NOT in the interior of any third disk B(c_j,r).

Three-disk reduction (this file):
  (i)  t_1..t_9 in (0, a], a = asin r, and sum_j 2 t_j >= 2 pi  (arcs cover the circle);
  (ii) for the pair (1,2) and a third disk j: the two uncovered gaps are covered by the
       remaining arcs, each of length <= 2a, giving
          far gap  <= 2 m a        (m = number of arcs between disk 2 and disk j)
          near gap <= 2 (6-m) a
  (iii) adjacent arcs overlap with private parts: o < 2 min(t,t').
The margin is  mu = |v_12 - c_3| - r  and O1 for this triple is  mu > 0.
Coordinates: centre c_k = rho(t_k) u(psi_k), rho(t) = cos t - sqrt(r^2 - sin^2 t).

PART 0 calibrates the instrument on the saved certified object (9 boundary disks).
PART 1 minimises mu over the domain by multistart SLSQP (bounded, no grids).
PART 2 builds an explicit completion to a legal 9-ring for the worst triple found and
       re-checks legality + O1 directly on the completed configuration.

All numeric; no certificate.
"""
import json
import math
import numpy as np
from scipy.optimize import minimize

S = 10 ** 17
ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"


def rho(t, r):
    return math.cos(t) - math.sqrt(max(r * r - math.sin(t) ** 2, 0.0))


def centre(t, psi, r):
    rr = rho(t, r)
    return (rr * math.cos(psi), rr * math.sin(psi))


def inner_crossing(c1, c2, r):
    dx, dy = c2[0] - c1[0], c2[1] - c1[1]
    D = math.hypot(dx, dy)
    if D <= 0:
        return None
    h = math.sqrt(max(r * r - D * D / 4, 0.0))
    mx, my = (c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2
    px, py = -dy / D, dx / D
    cand = [(mx - h * px, my - h * py), (mx + h * px, my + h * py)]
    return min(cand, key=lambda p: p[0] ** 2 + p[1] ** 2)


def outer_crossing(c1, c2, r):
    dx, dy = c2[0] - c1[0], c2[1] - c1[1]
    D = math.hypot(dx, dy)
    h = math.sqrt(max(r * r - D * D / 4, 0.0))
    mx, my = (c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2
    px, py = -dy / D, dx / D
    cand = [(mx - h * px, my - h * py), (mx + h * px, my + h * py)]
    return max(cand, key=lambda p: p[0] ** 2 + p[1] ** 2)


# ------------------------------------------------------------------ PART 0
def part0():
    print("=" * 78)
    print("PART 0 -- instrument calibration on the saved certified object (9 boundary disks)")
    print("=" * 78)
    J = json.load(open(ROOT + r"\n11\upper\certified_object.json", encoding="utf-8"))
    C = [(int(a) / S, int(b) / S) for a, b in J["centers_scaled_1e17"]]
    for r in (0.38, 0.3799838531198387090485182):
        rho_i = [math.hypot(*c) for c in C]
        bnd = sorted([i for i in range(11) if rho_i[i] >= 1 - r],
                     key=lambda i: math.atan2(C[i][1], C[i][0]))
        a = math.asin(r)
        ts, psis = [], []
        for i in bnd:
            phi = math.atan2(C[i][1], C[i][0])
            t = math.acos(max(-1, min(1, (1 + rho_i[i] ** 2 - r * r) / (2 * rho_i[i]))))
            ts.append(t); psis.append(phi)
        # consistency: the arc [psi-t, psi+t] must be covered by disk i exactly
        print("  r=%.12f  a=asin r=%.9f  sum 2t = %.9f (2pi=%.9f)  max t/a = %.6f"
              % (r, a, 2 * sum(ts), 2 * math.pi, max(ts) / a))
        # O1 margins on the true configuration -- third disk must be another RING disk
        # (the hub disks are supposed to contain the tips: that is O2, not O1).
        worst = None
        for k in range(9):
            i1, i2 = bnd[k], bnd[(k + 1) % 9]
            v = inner_crossing(C[i1], C[i2], r)
            assert v is not None
            for jj in bnd:
                if jj in (i1, i2):
                    continue
                mu = math.dist(v, C[jj]) - r
                if worst is None or mu < worst[0]:
                    worst = (mu, k, jj)
        print("      saved object: worst O1 margin (ring disks only) = %+.6e  (pair #%d vs ring disk %d)"
              % (worst[0], worst[1], worst[2]))
        # check that the inner/outer crossing classification matches |v|<1 iff o>0
        bad = 0
        for k in range(9):
            i1, i2 = bnd[k], bnd[(k + 1) % 9]
            o = ts[k] + ts[(k + 1) % 9] - ((psis[(k + 1) % 9] - psis[k]) % (2 * math.pi))
            v = inner_crossing(C[i1], C[i2], r); w = outer_crossing(C[i1], C[i2], r)
            if abs(o) < 1e-12 and abs(math.hypot(*w) - 1.0) > 1e-9:
                bad += 1
        print("      crossing-class control: ledgers with o=0 but |v_+| != 1 : %d" % bad)


# ------------------------------------------------------------------ PART 1
def margin_and_constraints(x, r, m):
    t1, t2, t3, o12, gf = x
    a = math.asin(r)
    d12 = t1 + t2 - o12
    psi1 = 0.0
    psi2 = psi1 + d12
    psi3 = psi2 + t2 + gf + t3
    c1 = centre(t1, psi1, r); c2 = centre(t2, psi2, r); c3 = centre(t3, psi3, r)
    v = inner_crossing(c1, c2, r)
    mu = math.dist(v, c3) - r
    gn = 2 * math.pi - (psi3 - psi1) - t1 - t3
    return mu, gn


def feasible_feas(x, r, m):
    t1, t2, t3, o12, gf = x
    a = math.asin(r)
    if not (1e-9 < t1 <= a and 1e-9 < t2 <= a and 1e-9 < t3 <= a):
        return False
    if not (0 <= o12 <= 2 * min(t1, t2) - 1e-12):
        return False
    _, gn = margin_and_constraints(x, r, m)
    if m == 0:
        if not (-(2 * min(t2, t3) - 1e-12) <= gf <= 0):
            return False
        return 0 <= gn <= 12 * a
    if m == 6:
        if not (0 <= gf <= 12 * a):
            return False
        return -(2 * min(t1, t3) - 1e-12) <= gn <= 0
    if not (0 <= gf <= 2 * m * a):
        return False
    return 0 <= gn <= 2 * (6 - m) * a


def part1(r, m, nstart=400, seed=0):
    a = math.asin(r)
    rng = np.random.default_rng(seed)
    best = None
    cons = [{"type": "ineq", "fun": lambda x: 2 * min(x[0], x[1]) - 1e-9 - x[3]}]
    for _ in range(nstart):
        t = rng.uniform(0.5 * a, a, 3)
        o = rng.uniform(0, 2 * min(t[0], t[1])) * 0.999
        if m == 0:
            gf = -rng.uniform(0, 2 * min(t[1], t[2]) * 0.999)
        elif m == 6:
            gf = rng.uniform(0, 12 * a)
        else:
            gf = rng.uniform(0, 2 * m * a)
        x0 = np.array([t[0], t[1], t[2], o, gf])
        if not feasible_feas(x0, r, m):
            # repair: shrink gf until the near gap is inside its budget
            for _ in range(60):
                mu, gn = margin_and_constraints(x0, r, m)
                lo, hi = (0, 12 * a) if m != 6 else (-(2 * min(x0[0], x0[2]) - 1e-9), 0)
                if m == 0:
                    lo, hi = -(2 * min(x0[1], x0[2]) - 1e-9), 0
                if lo <= x0[4] <= hi and lo <= gn <= hi:
                    break
                x0[4] = 0.5 * (x0[4] + (lo + hi) / 2)
            if not feasible_feas(x0, r, m):
                continue
        bnds = [(1e-9, a), (1e-9, a), (1e-9, a), (0, 2 * min(x0[0], x0[1])), (None, None)]
        res = minimize(lambda x: margin_and_constraints(x, r, m)[0], x0, bounds=bnds,
                       constraints=cons, method="SLSQP", options=dict(maxiter=300, ftol=1e-15))
        if not feasible_feas(res.x, r, m):
            continue
        val = margin_and_constraints(res.x, r, m)[0]
        if best is None or val < best[0]:
            best = (val, list(res.x), m)
    return best


# ------------------------------------------------------------------ PART 2
def complete_and_check(t1, t2, t3, o12, gf, r, m):
    """place the remaining six arcs (half-width a) to cover the two gaps; return ledger or None."""
    a = math.asin(r)
    d12 = t1 + t2 - o12
    psi = [0.0, d12, d12 + t2 + gf + t3]
    t = [t1, t2, t3]
    # far gap: from arc2 end to arc3 start, covered by m arcs (disks 3..j-1)
    L_end = psi[1] + t2
    R_start = psi[2] - t3
    for k in range(m):
        if m == 1:
            c = 0.5 * (L_end + R_start)
        else:
            c = L_end + a + (R_start - a - (L_end + a)) * k / (m - 1)
        psi.append(c); t.append(min(a, max(1e-6, 0.5 * (R_start - L_end) + a if False else a)))
    # near gap: from arc3 end to arc1 start (+2pi), covered by 6-m arcs
    L2 = psi[2] + t3
    R2 = 2 * math.pi - t1
    mm = 6 - m
    for k in range(mm):
        if mm == 1:
            c = 0.5 * (L2 + R2)
        else:
            c = L2 + a + (R2 - a - (L2 + a)) * k / (mm - 1)
        psi.append(c); t.append(a)
    # order by angle and check ledger conditions
    order = sorted(range(9), key=lambda i: psi[i])
    psi = [psi[i] for i in order]; t = [t[i] for i in order]
    ok = True
    o = []
    for k in range(9):
        d = (psi[(k + 1) % 9] - psi[k]) % (2 * math.pi)
        o.append(t[k] + t[(k + 1) % 9] - d)
    for k in range(9):
        if o[k] < -1e-9:
            ok = False
        priv = 2 * t[k] - o[k - 1] - o[k]
        if priv <= 1e-9:
            ok = False
    if not ok:
        return None
    C = [centre(t[k], psi[k], r) for k in range(9)]
    # direct O1 test over all adjacent pairs and all third disks
    worst = None
    for k in range(9):
        v = inner_crossing(C[k], C[(k + 1) % 9], r)
        for j in range(9):
            if j in (k, (k + 1) % 9):
                continue
            mu = math.dist(v, C[j]) - r
            if worst is None or mu < worst[0]:
                worst = (mu, k, j)
    return dict(t=t, psi=psi, o=o, C=C, worst=worst, ok=True)


if __name__ == "__main__":
    part0()
    print()
    print("=" * 78)
    print("PART 1 -- min margin over the three-disk domain (multistart SLSQP, no grids)")
    print("=" * 78)
    for r in (0.38, 0.376, 0.3710):
        print("  r = %.5f   a = asin r = %.6f" % (r, math.asin(r)))
        overall = None
        for m in range(7):
            b = part1(r, m, nstart=250, seed=1000 + m)
            if b is None:
                print("    m=%d : no feasible start" % m)
                continue
            print("    m=%d : min margin = %+.6e   at t=(%.6f,%.6f,%.6f) o12=%.6f gap=%.6f  (deg: %.3f,%.3f,%.3f)"
                  % (m, b[0], b[1][0], b[1][1], b[1][2], b[1][3], b[1][4],
                     *[math.degrees(v) for v in b[1][:3]]))
            if overall is None or b[0] < overall[0]:
                overall = b
        print("    --> overall min margin = %+.6e (m=%d)" % (overall[0], overall[2]))
        print()
        print("  PART 2 -- explicit completion of the worst triple to a legal 9-ring")
        comp = complete_and_check(overall[1][0], overall[1][1], overall[1][2], overall[1][3],
                                  overall[1][4], r, overall[2])
        if comp is None:
            print("    completion FAILED by the naive placement (ledger conditions not met)")
        else:
            print("    completion OK: sum 2t = %.9f, min o = %+.3e, min private = %+.3e"
                  % (2 * sum(comp["t"]), min(comp["o"]),
                     2 * min(comp["t"]) - max(comp["o"][k - 1] + comp["o"][k] for k in range(9))))
            print("    direct O1 on the completed legal 9-ring: worst margin = %+.6e (pair #%d vs disk %d)"
                  % (comp["worst"][0], comp["worst"][1], comp["worst"][2]))
