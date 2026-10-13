#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""audit_onehub.py -- independent audit of lead/K11-DUAL-EXCLUSION.md and
lead/onehub_interval_certificate.py (read-only on the lead's files).

Contents
  A  capture formula: independent derivation + exact/high-precision check
  B  domain and cover: parametrization, 12 segments, e-range, geometric necessity,
     no angle-wrap (periodicity check), corner/endpoint evaluation
  C  own box-cover of all 12 segments with the independent kernel kern80
     (exact Fractions, grid 2**-80, own pi/sin/cos/asin/acos) -- acceptance
     v.hi < pi_lo*(b0+h0)/11, no discarded nodes, midpoints exact rationals
  D  K1 weights nonnegativity, l>0, beta cut at 0, acos clip branch, sin(acos) vs
     sqrt(1-q^2) equivalence
  E  comparison with the recorded per-segment upper bounds

Usage: py -3 -B audit_onehub.py [segment_index ...]
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
N12 = HERE.parents[2]
import kern80 as K
from kern80 import Iv, hull, sqrt_iv, acos_iv, sincos_iv

OUT = HERE / "out"
OUT.mkdir(exist_ok=True)

U = F('0.361102963744508672616920293904')
EMAX = 3 * U - 1                              # hub norm upper bound
RL = 1 - U                                    # ring norm lower bound
RH = sqrt_iv(Iv(1 - U * U))                   # sqrt(1-U^2), interval
UIV = Iv(U, U)
EIV = Iv(EMAX) * Iv(0, 1)                     # not used directly; e = EMAX*q


def rho_iv(sA, sB):
    """rho = (1-U) + s*(sqrt(1-U^2)-(1-U)) over s in [sA,sB], enclosing interval"""
    return Iv(RL) + Iv(sA, sB) * (RH - Iv(RL))


def phi_iv(pA, pB):
    return K.TWO_PI * Iv(pA, pB)


def e_iv(qA, qB):
    return Iv(EMAX) * Iv(qA, qB)


def capture(rho, phi, e, wb, wh):
    """enclosure of C = b0 a + sin a (bc cos phi + bs sin phi)
                        + h0 b + sin b (hc dx/l + hs dy/l)
    Returns None if the enclosure cannot exclude l = 0."""
    b0, bc, bs = wb
    h0, hc, hs = wh
    co, si = sincos_iv(phi.lo, phi.hi)
    qa = (1 + rho * rho - UIV * UIV) / (2 * rho)
    if qa.lo < 0 or qa.hi > 1:
        qa = Iv(max(qa.lo, F(0)), min(qa.hi, F(1)))     # geometric: qa in [0,1]
    al = acos_iv(qa.lo, qa.hi)
    sa = sqrt_iv(Iv(1) - qa * qa)
    val = b0 * al + sa * (bc * co + bs * si)
    ell2 = rho * rho + e * e - 2 * rho * e * co
    if ell2.lo <= 0:
        return None
    ell = sqrt_iv(ell2)
    if ell.lo >= 2 * U:                                 # hub cap empty (l >= 2U)
        return val
    qb_lo = min(2 * U, ell.lo)
    qb_hi = ell.hi
    qb = Iv(min(qb_lo / (2 * U), F(1)), min(qb_hi / (2 * U), F(1)))
    be = acos_iv(qb.lo, qb.hi)
    sb = sqrt_iv(Iv(1) - qb * qb)
    dx = rho * co - e
    dy = rho * si
    return val + h0 * be + sb * (hc * dx / ell + hs * dy / ell)


def cover_segment(seg, wb, wh, qA, qB, maxboxes=400000, minwidth=F(1, 2 ** 62),
                  verbose=True):
    """own subdivision: returns dict with worst accepted upper and counters"""
    t0 = time.time()
    target_lo = K.PI.lo * (wb[0] + wh[0]) / 11
    stack = [((F(0), F(1)), (F(0), F(1)), (qA, qB))]
    n = leaves = 0
    worst = None
    while stack:
        sB_, pB_, qB_ = stack.pop()
        n += 1
        assert n <= maxboxes, ("budget", n, len(stack))
        v = None
        try:
            v = capture(rho_iv(*sB_), phi_iv(*pB_), e_iv(*qB_), wb, wh)
        except (ValueError, AssertionError):
            v = None
        if v is not None and v.hi < target_lo:
            leaves += 1
            if worst is None or v.hi > worst:
                worst = v.hi
            continue
        # split the widest normalised dimension: s and p over 1, q over (qB-qA)
        dims = [(sB_[1] - sB_[0], 0), (pB_[1] - pB_[0], 1),
                ((qB_[1] - qB_[0]) / (qB - qA), 2)]
        dims.sort(key=lambda z: z[0], reverse=True)
        kk = dims[0][1]
        boxes = [sB_, pB_, qB_]
        a, b = boxes[kk]
        assert b - a > minwidth, ("tiny box", kk, a, b)
        m = (a + b) / 2
        for pair in ((a, m), (m, b)):
            child = list(boxes)
            child[kk] = pair
            stack.append(tuple(child))
    dt = time.time() - t0
    if verbose:
        print("   seg q in [%s,%s]: boxes=%d leaves=%d worst=%s target_lo=%.12f margin=%.3e (%.1fs)"
              % (qA, qB, n, leaves, K.Iv(worst, worst).loose(16), float(target_lo),
                 float(target_lo - worst), dt), flush=True)
    return dict(boxes=n, leaves=leaves, worst_hi=str(worst), target_lo=str(target_lo),
                margin=float(target_lo - worst), seconds=dt)


def main():
    idxs = [int(a) for a in sys.argv[1:]] if len(sys.argv) > 1 else None
    ev = json.loads((N12 / "evidence" / "onehub-interval-all.json").read_text(encoding="utf-8"))
    inp = json.loads((N12 / "members" / "structure" / "onehub-dual" /
                      "segment_U_K1.json").read_text(encoding="utf-8"))
    rep = {"checks": {}, "segments": []}
    chk = rep["checks"]

    chk["evidence_exact_U_matches"] = (ev["exact_U"] ==
                                      "22568935234031792038557518369/62500000000000000000000000000")
    chk["twelve_segments"] = (len(ev["segments"]) == 12)
    # geometry constants
    chk["EMAX_positive"] = EMAX > 0
    chk["EMAX_lt_U"] = EMAX < U
    chk["hub_circle_inside_D"] = (EMAX + U < 1)              # e+U <= 4U-1 < 1
    chk["rhoplus_e_distance_positive"] = (RL - EMAX > 0)     # l >= 2-4U
    rep["numbers"] = dict(U=str(U), EMAX=str(EMAX), RL=str(RL),
                          RHL=RH.lo and str(RH.lo), two_minus_4U=str(2 - 4 * U))

    # ---- A: capture formula vs direct quadrature ----
    import mpmath as mp
    mp.mp.dps = 60

    def mf(x):
        return mp.mpf(x.numerator) / x.denominator

    rng = __import__("random").Random(11)
    formula_ok = True
    n_formula = 0
    for _ in range(12):
        b0, bc, bs = [F(rng.randint(-100, 100), 25) for _ in range(3)]
        h0, hc, hs = [F(rng.randint(-100, 100), 25) for _ in range(3)]
        rho = F(rng.randint(36, 90), 100)
        phi = F(rng.randint(0, 628), 100)
        e = F(rng.randint(0, 8), 100)
        qa = (1 + rho * rho - U * U) / (2 * rho)
        if not (0 <= qa <= 1):
            continue
        rho_m, e_m, ph = mf(rho), mf(e), mf(phi)
        al = mp.acos(mf(qa))
        ell = mp.sqrt(rho_m ** 2 + e_m ** 2 - 2 * rho_m * e_m * mp.cos(ph))
        fW = lambda t: (mf(b0) + mf(bc) * mp.cos(t) + mf(bs) * mp.sin(t)) / 2
        q1 = mp.quad(fW, [ph - al, ph + al])
        ratio = ell / (2 * mf(U))
        bet = mp.acos(min(mp.mpf(1), ratio))
        dcos = (rho_m * mp.cos(ph) - e_m) / ell
        dsin = (rho_m * mp.sin(ph)) / ell
        psi = mp.atan2(dsin, dcos)
        fV = lambda t: (mf(h0) + mf(hc) * mp.cos(t) + mf(hs) * mp.sin(t)) / 2
        q2 = mp.quad(fV, [psi - bet, psi + bet])
        direct = q1 + q2
        closed = (mf(b0) * al + mp.sin(al) * (mf(bc) * mp.cos(ph) + mf(bs) * mp.sin(ph))
                  + mf(h0) * bet + mp.sin(bet) * (mf(hc) * dcos + mf(hs) * dsin))
        formula_ok &= abs(direct - closed) < mp.mpf('1e-40')
        n_formula += 1
    chk["capture_formula_matches_quadrature"] = bool(formula_ok)
    rep["numbers"]["n_formula_cases"] = n_formula

    # ---- B: domain, e-range, periodicity, corners ----
    e_intervals = [tuple(F(x) for x in s["e_fraction"]) for s in ev["segments"]]
    chk["e_intervals_adjacent_and_cover"] = all(
        e_intervals[i][1] == e_intervals[i + 1][0] for i in range(11)) and \
        e_intervals[0][0] == 0 and e_intervals[-1][1] == 1
    def pre(seg):
        rows = seg["weights"]
        d = {"boundary": [F(0)] * 3, "hub": [F(0)] * 3}
        for row in rows:
            v = F(round(F(str(row["weight"])) * 10 ** 9), 10 ** 9)
            assert v >= 0
            circ = row["row"].split("_")[0]
            d[circ][0] += v
            if "cos" in row["row"]:
                d[circ][1] += v * int(row["row"].split("_")[-1])
            if "sin" in row["row"]:
                d[circ][2] += v * int(row["row"].split("_")[-1])
        return (d["boundary"][0], d["boundary"][1], d["boundary"][2]), \
            (d["hub"][0], d["hub"][1], d["hub"][2])
    nonneg = True
    for seg in ev["segments"]:
        wb, wh = ([F(x) for x in seg["weights"]["boundary"]],
                  [F(x) for x in seg["weights"]["hub"]])
        nonneg &= (wb[0] >= abs(wb[1]) + abs(wb[2]))
        nonneg &= (wh[0] >= abs(wh[1]) + abs(wh[2]))
    chk["K1_weights_nonnegative_sufficient"] = nonneg
    # recorded target = pi(b0+h0)/11 (check with the pi enclosure)
    tgt_ok = True
    for seg in ev["segments"]:
        wb, wh = ([F(x) for x in seg["weights"]["boundary"]],
                  [F(x) for x in seg["weights"]["hub"]])
        lo, hi = [F(x) for x in seg["target"].strip("[]").split(",")]
        t = K.PI * Iv(wb[0] + wh[0]) / 11
        tgt_ok &= (t.lo <= hi and lo <= t.hi)
    chk["recorded_target_contains_pi_b0h0_over_11"] = tgt_ok
    # periodicity / no wrap: C(phi=0) vs C(phi=2pi), and at the 8 corners
    wrap_ok = True
    corner_ok = True
    corner_rows = []
    for i, seg in enumerate(ev["segments"]):
        wb, wh = ([F(x) for x in seg["weights"]["boundary"]],
                  [F(x) for x in seg["weights"]["hub"]])
        qA, qB = e_intervals[i]
        target_lo = K.PI.lo * (wb[0] + wh[0]) / 11
        for s in (F(0), F(1)):
            c0 = capture(rho_iv(s, s), phi_iv(F(0), F(0)), e_iv(qA, qA), wb, wh)
            c2 = capture(rho_iv(s, s), phi_iv(F(1), F(1)), e_iv(qA, qA), wb, wh)
            wrap_ok &= c0.overlap(c2) and abs(c0.hi - c2.hi) < F(1, 10 ** 15)
        for s in (F(0), F(1)):
            for p in (F(0), F(1)):
                for q in (qA, qB):
                    v = capture(rho_iv(s, s), phi_iv(p, p), e_iv(q, q), wb, wh)
                    ok = v.hi < target_lo
                    corner_ok &= ok
                    if not ok:
                        corner_rows.append(dict(seg=i, s=str(s), p=str(p), q=str(q),
                                                v=v.loose(16)))
    chk["no_angle_wrap_periodicity"] = bool(wrap_ok)
    chk["corner_points_below_target"] = bool(corner_ok)

    # ---- C: own box cover ----
    segs = []
    for i, seg in enumerate(ev["segments"]):
        if idxs is not None and i not in idxs:
            continue
        wb, wh = ([F(x) for x in seg["weights"]["boundary"]],
                  [F(x) for x in seg["weights"]["hub"]])
        qA, qB = e_intervals[i]
        r = cover_segment(seg, wb, wh, qA, qB)
        r.update(segment=i, recorded_upper=seg["upper"], recorded_target=seg["target"])
        rec_hi = F(seg["upper"].strip("[]").split(",")[1])
        r["my_worst_ge_recorded"] = bool(F(r["worst_hi"]) >= rec_hi - F(1, 10 ** 12))
        segs.append(r)
    rep["segments"] = segs
    rep["kernel_gap_stats"] = dict(K.GAP_STATS)
    rep["kernel_fix_note"] = ("critical-point condition = enclosure INTERSECTS [a,b] "
                              "(post-fix); the counters record how many +-1 insertions "
                              "a containment-only test would have missed in this run")
    allok = all(s["margin"] > 0 for s in segs) if segs else None
    chk["own_cover_all_listed_segments"] = bool(allok) if segs else None

    (OUT / "onehub-audit.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False,
                                                     default=str), encoding="utf-8")
    print("\nchecks:")
    for k, v in chk.items():
        print("  %s  %s" % ("PASS" if v else ("FAIL" if v is False else "info"), k))
    print("log ->", OUT / "onehub-audit.json")
    if any(v is False for v in chk.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
