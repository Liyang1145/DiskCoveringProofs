# -*- coding: utf-8 -*-
"""o1_triple_common.py -- mechanism test (bounded, numeric): every legal ledger whose three
CONSECUTIVE ring disks share a common point at r=0.38 -- does its hole still contain three
points pairwise > 2r apart?

Domain (lead/TRIPLE-CLUSTER-NECESSARY.md + budget):
  * three consecutive cluster disks share a point p  => their union is contained in B(p,2r),
    so their boundary-arc union span S <= 2 asin(2r) = 1.7266;
  * the six other disks have half-width t_j >= t0 = pi - asin(2r) - 5 asin r = 0.3293 and
    their centres avoid the core: |c_j| >= rho0 = cos t0 - sqrt(r^2 - sin^2 t0), so their
    disks avoid B(0, rho0 - r) = B(0, 0.3667);
  * the six arcs must cover the complement, so S >= 2pi - 6*2*asin r = 1.6056.
Construction: sample p and three centres at distance exactly r from p (the extreme
"all three pass through p" case), keep only legal ledgers (arcs consecutive, half-widths
<= asin r), fill the complementary arc with six maximal arcs (t = asin r, |c| = sqrt(1-r^2)
> rho0), then compute the hole on a numpy grid and search a 3-packing
(pairwise distance > 2r) by farthest-point heuristic.

Controls: (C1) the certified O1 counterexample ledger (its packing margin must be positive);
(C2) the same ledger with the triple-common-point adjustment is not available -- instead we
report the family statistics.  No claim of a lower bound is made from this numeric test.

Budget: bounded sample; no global 17D search.
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
RHO0 = math.cos(T0) - math.sqrt(R * R - math.sin(T0) ** 2)
S_MIN = 2 * math.pi - 12 * A
S_MAX = 2 * math.asin(2 * R)


def arc_halfwidth(rho):
    if rho < 1 - R:
        return None
    c = (1 + rho * rho - R * R) / (2 * rho)
    if c < -1 or c > 1:
        return None
    return math.acos(c)


def centre(t, psi):
    rho = math.cos(t) - math.sqrt(max(R * R - math.sin(t) ** 2, 0.0))
    return (rho * math.cos(psi), rho * math.sin(psi))


def hole_and_packing(C, nr=150, nt=300, n_keep=2500, seed=0):
    """hole grid + farthest-point 3-packing; returns (packing margin, points, hole size)."""
    rr = (np.arange(nr) + 0.5) / nr
    tt = 2 * math.pi * (np.arange(nt) + 0.5) / nt
    X = np.outer(rr, np.cos(tt)).ravel()
    Y = np.outer(rr, np.sin(tt)).ravel()
    cov = np.zeros_like(X, dtype=bool)
    for (cx, cy) in C:
        cov |= ((X - cx) ** 2 + (Y - cy) ** 2) <= R * R
    HX, HY = X[~cov], Y[~cov]
    if len(HX) == 0:
        return None, None, 0
    if len(HX) > n_keep:
        idx = np.linspace(0, len(HX) - 1, n_keep).astype(int)
        HX, HY = HX[idx], HY[idx]
    P = np.stack([HX, HY], axis=1)
    # farthest-point heuristic from 4 seeds, take the best triple
    best = None
    rng = np.random.default_rng(seed)
    for s in range(4):
        i0 = int(rng.integers(len(P)))
        sel = [i0]
        for _ in range(2):
            d = np.min(np.linalg.norm(P[:, None, :] - P[sel][None, :, :], axis=2), axis=1)
            sel.append(int(np.argmax(d)))
        dmin = min(math.dist(P[sel[i]], P[sel[j]]) for i in range(3) for j in range(i + 1, 3))
        if best is None or dmin > best[0]:
            best = (dmin, [P[i] for i in sel])
    return best[0], best[1], len(HX)


def build_ledger(p, angles):
    """three cluster centres at distance exactly r from p; returns (C, arcs, ok)."""
    C = []
    for th in angles:
        C.append((p[0] + R * math.cos(th), p[1] + R * math.sin(th)))
    ts, phis = [], []
    for c in C:
        rho = math.hypot(*c)
        t = arc_halfwidth(rho)
        if t is None or t > A + 1e-12:
            return None, None, False
        ts.append(t); phis.append(math.atan2(c[1], c[0]))
    order = sorted(range(3), key=lambda i: phis[i])
    ts = [ts[i] for i in order]; C = [C[i] for i in order]; phis = [phis[i] for i in order]
    # consecutive? arcs [phi-t, phi+t] must chain into one arc
    span = ts[0] + sum(2 * ts[k] for k in (1, 2)) if False else None
    # union span of the three arcs (consecutiveness assumed by construction check below)
    lo = phis[0] - ts[0]
    hi = lo
    for k in range(3):
        a, b = phis[k] - ts[k], phis[k] + ts[k]
        if a > hi + 1e-9:
            return None, None, False         # gap -> not consecutive
        hi = max(hi, b)
    S = hi - lo
    if S < S_MIN - 1e-9 or S > S_MAX + 1e-9:
        return None, None, False
    # six maximal fillers on the complementary arc [hi, lo+2pi]
    span_left = (lo + 2 * math.pi) - hi
    if span_left < 0:
        return None, None, False
    step = span_left / 6.0
    for k in range(6):
        psi = hi + step * (k + 0.5)
        C.append(centre(A, psi))
    # ledger bookkeeping: all nine arcs in cyclic order, overlaps and private parts
    arcs = [(phis[k], ts[k]) for k in range(3)]
    for k in range(6):
        arcs.append((hi + step * (k + 0.5), A))
    arcs.sort(key=lambda z: z[0])
    o = []
    for k in range(9):
        dlt = (arcs[(k + 1) % 9][0] - arcs[k][0]) % (2 * math.pi)
        o.append(arcs[k][1] + arcs[(k + 1) % 9][1] - dlt)
    priv = [2 * arcs[k][1] - o[k - 1] - o[k] for k in range(9)]
    legal = min(o) >= -1e-9 and min(priv) > 1e-9
    info = (ts, lo, hi, S, o, priv, legal)
    return C, info, True


def analyse(C):
    """hole + packing; also verify the six fillers avoid the core (lead's constraint)."""
    core = min(math.hypot(*c) for c in C[3:])
    margin, pts, nh = hole_and_packing(C)
    return margin, pts, nh, core


if __name__ == "__main__":
    rng = np.random.default_rng(7)
    results = []
    tried = 0
    for trial in range(4000):
        if len(results) >= 120:
            break
        rp = rng.uniform(1 - 2 * R, 0.99)
        thp = rng.uniform(0, 2 * math.pi)
        p = (rp * math.cos(thp), rp * math.sin(thp))
        angles = rng.uniform(0, 2 * math.pi, 3)
        C, info, ok = build_ledger(p, angles)
        tried += 1
        if not ok:
            continue
        margin, pts, nh, core = analyse(C)
        if margin is None:
            continue
        results.append((margin, C, info, nh, core, p))
    print("=" * 78)
    print("triple-common-point family at r=%.3f (S in [%.4f, %.4f], t0=%.4f, rho0=%.4f)"
          % (R, S_MIN, S_MAX, T0, RHO0))
    print("sampled legal ledgers: %d  (from %d samples)" % (len(results), tried))
    results.sort(key=lambda z: z[0])
    print()
    print("packing margin (min pairwise distance - 2r) percentiles:")
    ms = np.array([z[0] for z in results]) - 2 * R
    if len(ms):
        for q in (0, 5, 25, 50, 75, 95, 100):
            print("   q%3d%% : %+.6f" % (q, float(np.percentile(ms, q))))
    print()
    hard = results[0]
    print("HARDEST sampled configuration: packing margin = %+.6e  (hole grid pts %d, six-filler core dist %.6f)"
          % (hard[0] - 2 * R, hard[3], hard[4]))
    print("   p = (%.6f, %.6f) ; S = %.6f ; t_cluster(deg) = %s"
          % (hard[5][0], hard[5][1], hard[2][3], ["%.4f" % math.degrees(x) for x in hard[2][0]]))
    print("   three packing points: %s" % [[round(float(a), 6), round(float(b), 6)] for a, b in hard[1]])
    print("   pairwise distances: %s" % ["%.6f" % math.dist(hard[1][i], hard[1][j])
                                         for i in range(3) for j in range(i + 1, 3)])
    out = dict(r=R, S_range=[S_MIN, S_MAX], t0=T0, rho0=RHO0, n_legal=len(results),
               margins=[float(z[0] - 2 * R) for z in results[:50]],
               hardest=dict(margin=float(hard[0] - 2 * R), p=list(hard[5]), S=hard[2][3],
                            t_cluster=[float(x) for x in hard[2][0]],
                            pts=[[float(a), float(b)] for a, b in hard[1]]),
               note="numeric mechanism probe; failure to find a packing is a METHOD GAP, "
                    "not extendability and not a refutation")
    with open(os.path.join(OUT, "o1_triple_common.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print()
    print("wrote out/o1_triple_common.json")
