# -*- coding: utf-8 -*-
"""o1_deficit_probe.py -- bounded probe (<=10 min): can the empty-circle mechanism extend to
the WHOLE triple-common-point family once the six non-cluster disks carry a real deficit?

New constraint (lead): the six disks cannot all be maximal.  With the cluster's union span
capped by the common point (S <= 2 asin(2r)) and the six arcs having to cover the complement,
      sum_j t_j >= pi - asin(2r)   =>   total deficit  D = 6 asin r - sum_j t_j <= Dmax,
      Dmax = asin(2r) + 6 asin r - pi = 0.06049824...,  and  t_j >= t0 = pi - asin(2r) - 5 asin r.
Deficit modes: spread over 6 / over 2 / concentrated on 1 (extremal) / random.
The three cluster arcs are legalised with the remaining budget; the TRUE common-point
condition (min_x max_i |x - c_i| <= r) is checked directly, not assumed.

Output: worst hole-circle margin (d* - 2r, d* = max_z min_i|z-c_i| s.t. |z| + d* - r <= 1) and
a complete legal ledger JSON.  Stop as soon as d* <= 2r or 200 legal triple samples are reached.

Method gap: a numeric sample of a sub-family; success does not certify and failure would not
refute the triple exclusion.  Two sufficient conditions (3-packing vs empty circle) are NOT
comparable: circle>r does not imply a 3-packing (that needs s > 2r/sqrt3), nor conversely.
"""
import json
import math
import os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
R = 0.38
A = math.asin(R)
T0 = math.pi - math.asin(2 * R) - 5 * A
DMAX = math.asin(2 * R) + 6 * A - math.pi
S_MAX = 2 * math.asin(2 * R)


def rho(t):
    return math.cos(t) - math.sqrt(max(R * R - math.sin(t) ** 2, 0.0))


def cen(t, psi):
    rr = rho(t)
    return (rr * math.cos(psi), rr * math.sin(psi))


def hole_circle(C, nz=180, nt=360):
    zr = (np.arange(nz) + 0.5) / nz
    zt = 2 * math.pi * (np.arange(nt) + 0.5) / nt
    X = np.outer(zr, np.cos(zt)).ravel(); Y = np.outer(zr, np.sin(zt)).ravel()
    D = np.full(X.shape, 1e9)
    for (cx, cy) in C:
        D = np.minimum(D, np.hypot(X - cx, Y - cy))
    feas = (np.hypot(X, Y) + D - R) <= 1.0
    order = np.argsort(-np.where(feas, D, -1))
    best = (-1.0, None)
    for seed in order[:25]:
        z = np.array([X[seed], Y[seed]]); step = 0.02
        for _ in range(150):
            cand = []
            for dx in (-step, 0, step):
                for dy in (-step, 0, step):
                    zz = z + np.array([dx, dy])
                    dd = min(math.dist(zz, c) for c in C)
                    if math.hypot(*zz) + dd - R <= 1.0:
                        cand.append((dd, zz))
            if not cand:
                break
            cand.sort(key=lambda t: -t[0])
            if cand[0][0] <= min(math.dist(z, c) for c in C) + 1e-15:
                step *= 0.5
                if step < 1e-6:
                    break
            z = cand[0][1]
        dd = min(math.dist(z, c) for c in C)
        if dd > best[0]:
            best = (dd, z)
    return best


def common_point_radius(C3):
    """min_x max_i |x - c_i| over the three cluster centres (multi-start local search)."""
    best = 1e9
    seeds = [(0.0, 0.0)] + [(0.3 * math.cos(2 * math.pi * k / 8), 0.3 * math.sin(2 * math.pi * k / 8)) for k in range(8)]
    seeds += list(C3)
    for s in seeds:
        x = np.array(s, dtype=float); step = 0.05
        for _ in range(120):
            cur = max(math.dist(x, c) for c in C3)
            improved = False
            for dx in (-step, 0, step):
                for dy in (-step, 0, step):
                    y = x + np.array([dx, dy])
                    v = max(math.dist(y, c) for c in C3)
                    if v < cur - 1e-15:
                        x, cur, improved = y, v, True
            if not improved:
                step *= 0.5
                if step < 1e-7:
                    break
        best = min(best, max(math.dist(x, c) for c in C3))
    return best


def build(p, angles, mode, rng):
    C3 = [(p[0] + R * math.cos(t), p[1] + R * math.sin(t)) for t in angles]
    ts, phis = [], []
    for c in C3:
        rr_ = math.hypot(*c)
        if rr_ < 1 - R:
            return None
        cth = (1 + rr_ * rr_ - R * R) / (2 * rr_)
        if cth < -1 or cth > 1:
            return None
        t = math.acos(cth)
        if t > A + 1e-12:
            return None
        ts.append(t); phis.append(math.atan2(c[1], c[0]))
    order = sorted(range(3), key=lambda i: phis[i])
    ts = [ts[i] for i in order]; phis = [phis[i] for i in order]; C3 = [C3[i] for i in order]
    lo = phis[0] - ts[0]; hi = lo
    for k in range(3):
        a, b = phis[k] - ts[k], phis[k] + ts[k]
        if a > hi + 1e-9:
            return None                       # cluster arcs not consecutive
        hi = max(hi, b)
    S = hi - lo
    if S > S_MAX + 1e-9:
        return None
    # six deficits
    D = DMAX * rng.uniform(0.6, 1.0) if mode != "spread6" else DMAX * rng.uniform(0.9, 1.0)
    if mode == "one":
        dlt = [D, 0, 0, 0, 0, 0]
    elif mode == "two":
        dlt = [D / 2, D / 2, 0, 0, 0, 0]
    elif mode == "six":
        dlt = [D / 6] * 6
    else:
        w = rng.dirichlet(np.ones(6)) * D
        dlt = list(w)
    t6 = [A - x for x in dlt]
    if min(t6) < T0 - 1e-12:
        return None
    if S < 2 * math.pi - 2 * sum(t6) - 1e-9:
        return None                            # six arcs cannot cover the complement
    # place the six to tile the complement [hi, lo+2pi]
    span = (lo + 2 * math.pi) - hi
    slack = 2 * sum(t6) - span
    ov = slack / 5.0 if slack > 0 else 0.0
    C = list(C3); cur = hi
    for k in range(6):
        C.append(cen(t6[k], cur + t6[k]))
        cur += 2 * t6[k] - ov
    arcs = [(phis[k], ts[k]) for k in range(3)]
    cur = hi
    for k in range(6):
        arcs.append((cur + t6[k], t6[k]))
        cur += 2 * t6[k] - ov
    arcs.sort(key=lambda z: z[0])
    o = []
    for k in range(9):
        d = (arcs[(k + 1) % 9][0] - arcs[k][0]) % (2 * math.pi)
        o.append(arcs[k][1] + arcs[(k + 1) % 9][1] - d)
    priv = [2 * arcs[k][1] - o[k - 1] - o[k] for k in range(9)]
    legal = min(o) >= -1e-9 and min(priv) > 1e-9
    return dict(C=C, C3=C3, t3=ts, t6=t6, S=S, dlt=dlt, o=o, priv=priv, legal=legal)


if __name__ == "__main__":
    rng = np.random.default_rng(23)
    modes = ["spread6", "two", "one", "six", "rand"]
    rows = []
    tried = 0
    stop_reason = "sample cap"
    while len(rows) < 200 and tried < 150000:
        tried += 1
        mode = modes[tried % len(modes)]
        # bias p inward: small |p| gives large cluster arcs and hence the large union span S
        # that the six-disk deficit forces (S >= 2pi - 2 sum t6 = 1.6056 + 2D).
        rp = rng.uniform(1 - 2 * R, 0.99)
        thp = rng.uniform(0, 2 * math.pi)
        p = (rp * math.cos(thp), rp * math.sin(thp))
        angles = rng.uniform(0, 2 * math.pi, 3)
        st = build(p, angles, mode, rng)
        if st is None or not st["legal"]:
            continue
        cp = common_point_radius(st["C3"])
        if cp > R + 1e-9:
            continue                       # no true common point -> not in the subclass
        dstar, z = hole_circle(st["C"])
        margin = dstar - 2 * R
        rows.append((margin, dstar, z, st, cp, mode))
        if margin <= 0:
            stop_reason = "FOUND d* <= 2r"
            break
    rows.sort(key=lambda t: t[0])
    ms = np.array([t[0] for t in rows]) if rows else np.array([])
    print("=" * 78)
    print("deficit-constrained triple-common-point probe   (Dmax = %.8f, t0 = %.8f)" % (DMAX, T0))
    print("stop reason: %s ; legal samples: %d (from %d tries)" % (stop_reason, len(rows), tried))
    if len(ms):
        for q in (0, 5, 25, 50, 75, 95, 100):
            print("   d* - 2r  q%3d%% = %+.6f" % (q, float(np.percentile(ms, q))))
        worst = rows[0]
        print("HARDEST: margin = %+.6e  d* = %.9f  z* = (%.6f, %.6f)  mode = %s" %
              (worst[0], worst[1], worst[2][0], worst[2][1], worst[5]))
        print("   S = %.6f (bound %.6f) ; t3(deg) = %s ; deficit = %.8f (bound %.8f) ; common-point radius = %.9f <= r ? %s"
              % (worst[3]["S"], S_MAX, ["%.4f" % math.degrees(x) for x in worst[3]["t3"]],
                 sum(worst[3]["dlt"]), DMAX, worst[4], worst[4] <= R + 1e-9))
        print("   ledger: min overlap = %+.3e ; min private = %+.6f" % (min(worst[3]["o"]), min(worst[3]["priv"])))
        ledger = dict(r=R, mode=worst[5], t=[float(x) for x in (list(worst[3]["t3"]) + list(worst[3]["t6"]))],
                      centres=[[float(a), float(b)] for a, b in worst[3]["C"]],
                      overlaps=[float(x) for x in worst[3]["o"]], private=[float(x) for x in worst[3]["priv"]],
                      S=float(worst[3]["S"]), deficit=float(sum(worst[3]["dlt"])),
                      common_point_radius=float(worst[4]), dstar=float(worst[1]),
                      zstar=[float(worst[2][0]), float(worst[2][1])], margin=float(worst[0]),
                      note="numeric probe ledger (mode=deficit distribution); legality is checked "
                           "numerically (overlaps>=0, private>0, true common point <= r)")
        with open(os.path.join(OUT, "o1_deficit_ledger.json"), "w", encoding="utf-8") as f:
            json.dump(ledger, f, indent=1)
        print("   wrote out/o1_deficit_ledger.json")
    out = dict(r=R, Dmax=DMAX, t0=T0, stop_reason=stop_reason, n=len(rows), tried=tried,
               margins=[float(t[0]) for t in rows[:80]],
               worst=None if not len(ms) else dict(margin=float(rows[0][0]), dstar=float(rows[0][1]),
                                                   mode=rows[0][5]), note="numeric; not a certification")
    with open(os.path.join(OUT, "o1_deficit_probe.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print("wrote out/o1_deficit_probe.json")
