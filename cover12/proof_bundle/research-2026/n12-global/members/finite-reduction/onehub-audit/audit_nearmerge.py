#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""audit_nearmerge.py -- independent audit of the delta-near-merge capacity step
(lead/nearmerge_interval_certificate.py + evidence/nearmerge-interval-1-20*.json).

Two parts:
  Part I  the CHANGED beta domain (the lead's specific question): for the circle
          S(h,R) with R = U+delta, a ring disk of radius U at distance l = |c-h|
          covers exactly the arc of half-width beta = acos(clip(l^2+R^2-U^2, 2 R l))
          where clip keeps the argument in [-1,1].  Checked by direct geometry
          (fine-grid / bisection of |R u_psi - c| <= U) and by exact algebra:
            * the full-circle branch needs l+R <= U, impossible since
              rho + R >= 1-U + U + delta > U                        (inner branch empty)
            * qb >= sqrt(1-(U/R)^2) > 0 and qb <= 1, so beta in [0, pi/2]
            * the cut l >= R+U gives qb >= 1, i.e. beta = 0 (empty cap)
  Part II an independent box cover of selected segments with my own kernel.

Usage: py -3 -B audit_nearmerge.py [segment ...]
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
N12 = HERE.parents[2]
sys.path.insert(0, str(HERE))
import kern80 as K
from kern80 import Iv, sqrt_iv, acos_iv, sincos_iv, hull

OUT = HERE / "out"
U = F('0.361102963744508672616920293904')
DEL = F(1, 20)
R = U + DEL
EM = 3 * U - 1 + DEL
RL = 1 - U
RH = sqrt_iv(Iv(1 - U * U))


def rho_iv(a, b):
    return Iv(RL) + Iv(a, b) * (RH - Iv(RL))


def capture_nm(rho, phi, e, wb, wh):
    b0, bc, bs = wb
    h0, hc, hs = wh
    co, si = sincos_iv(phi.lo, phi.hi)
    qa = (1 + rho * rho - Iv(U) * Iv(U)) / (2 * rho)
    if qa.lo < 0 or qa.hi > 1:
        qa = Iv(max(qa.lo, F(0)), min(qa.hi, F(1)))
    al = acos_iv(qa.lo, qa.hi)
    sa = sqrt_iv(Iv(1) - qa * qa)
    val = b0 * al + sa * (bc * co + bs * si)
    ell2 = rho * rho + e * e - 2 * rho * e * co
    if ell2.lo <= 0:
        return None
    ell = sqrt_iv(ell2)
    if ell.lo >= R + U:                       # no intersection with S(h,R)
        return val
    qb = (Iv(R) * Iv(R) + ell2 - Iv(U) * Iv(U)) / (2 * Iv(R) * ell)
    qb = Iv(min(qb.lo, F(1)), min(qb.hi, F(1)))
    be = acos_iv(qb.lo, qb.hi)
    sb = sqrt_iv(Iv(1) - qb * qb)
    return val + h0 * be + sb * (hc * (rho * co - e) / ell + hs * (rho * si) / ell)


def cover(seg_weights, qA, qB, load, nrings, maxboxes=600000, minwidth=F(1, 2 ** 62)):
    import time
    t0 = time.time()
    wb, wh = seg_weights
    target_lo = K.PI.lo * (wb[0] + wh[0]) / load
    cap = capture_nm if nrings == 10 else None
    stack = [((F(0), F(1)), (F(0), F(1)), (qA, qB))]
    n = leaves = 0
    worst = None
    while stack:
        sB, pB, qBx = stack.pop()
        n += 1
        assert n <= maxboxes, ("budget", n, len(stack))
        try:
            v = cap(rho_iv(*sB), K.TWO_PI * Iv(*pB), Iv(EM) * Iv(*qBx), wb, wh)
        except (ValueError, AssertionError):
            v = None
        if v is not None and v.hi < target_lo:
            leaves += 1
            if worst is None or v.hi > worst:
                worst = v.hi
            continue
        dims = [(sB[1] - sB[0], 0), (pB[1] - pB[0], 1), ((qBx[1] - qBx[0]) / (qB - qA), 2)]
        dims.sort(key=lambda z: z[0], reverse=True)
        kk = dims[0][1]
        boxes = [sB, pB, qBx]
        a, b = boxes[kk]
        assert b - a > minwidth, ("tiny box", kk, a, b)
        m = (a + b) / 2
        for pair in ((a, m), (m, b)):
            child = list(boxes)
            child[kk] = pair
            stack.append(tuple(child))
    print("   nm seg q in [%s,%s]: boxes=%d leaves=%d worst=%s target_lo=%.12f "
          "margin=%.3e (%.1fs)" % (qA, qB, n, leaves, str(worst)[:20], float(target_lo),
                                   float(target_lo - worst), time.time() - t0), flush=True)
    return dict(boxes=n, leaves=leaves, worst=str(worst), target_lo=str(target_lo),
                margin=float(target_lo - worst))


def main():
    rep, chk = {}, {}
    ev = json.loads((N12 / "evidence" / "nearmerge-interval-1-20.json").read_text(encoding="utf-8"))
    ev2 = json.loads((N12 / "evidence" / "nearmerge-interval-1-20-tail.json").read_text(encoding="utf-8"))
    segs = ev["segments"] + ev2["segments"]

    # ---------- Part I: the changed beta domain ----------
    import mpmath as mp
    mp.mp.dps = 60

    def mf(x):
        return mp.mpf(x.numerator) / x.denominator

    # (a) exact algebra: qb bounds over the whole domain
    #     qb(ell) = (R^2+ell^2-U^2)/(2 R ell) has minimum sqrt(1-(U/R)^2) at ell=sqrt(R^2-U^2)
    qb_min_theory = mp.sqrt(1 - (mf(U) / (mf(U) + mf(DEL))) ** 2)
    rep["qb_min_theory"] = mp.nstr(qb_min_theory, 20)
    rep["beta_max_theory_deg"] = mp.nstr(mp.degrees(mp.acos(qb_min_theory)), 10)
    chk["qb_min_positive"] = bool(qb_min_theory > 0)
    chk["beta_max_below_90deg"] = bool(mp.acos(qb_min_theory) < mp.pi / 2)
    # full-circle branch would need ell + R <= U ; here ell >= rho - e >= 2-4U-delta
    chk["ell_lower_bound_exceeds_U_minus_R"] = bool((2 - 4 * U - DEL) + R > U)
    chk["ell_lower_bound_gt_delta"] = bool(2 - 4 * U - DEL > DEL)

    # (b) direct geometry: measure the cap by brute force and compare with 2*beta
    rng = __import__("random").Random(31)
    geo_ok = True
    geo_rows = []
    for _ in range(10):
        rho = F(rng.randint(36, 87), 100)
        e = EM * F(rng.randint(0, 20), 100)
        ph = 2 * mp.pi * mf(F(rng.randint(0, 100), 100))
        l = mp.sqrt(mf(rho) ** 2 + mf(e) ** 2 - 2 * mf(rho) * mf(e) * mp.cos(ph))
        if l >= mf(R) + mf(U) or l <= 0:
            continue
        qb = (mf(R) ** 2 + l ** 2 - mf(U) ** 2) / (2 * mf(R) * l)
        beta = mp.acos(min(mp.mpf(1), max(mp.mpf(-1), qb)))
        # direction of c-h
        psi_c = mp.atan2(mf(rho) * mp.sin(ph), mf(rho) * mp.cos(ph) - mf(e))
        # brute force: fraction of the circle inside the disk (closed cap measure)
        N = 200000
        cnt = 0
        for i in range(N):
            psi = 2 * mp.pi * i / N
            d = mp.sqrt((mf(R) * mp.cos(psi) - (mf(rho) * mp.cos(ph) - mf(e))) ** 2
                        + (mf(R) * mp.sin(psi) - mf(rho) * mp.sin(ph)) ** 2)
            if d <= mf(U):
                cnt += 1
        measure = 2 * mp.pi * mp.mpf(cnt) / N
        # sanity: the cap is symmetric about psi_c
        sym_ok = abs(((psi_c - beta) % (2 * mp.pi)) - psi_c + beta) < 1e-9 if beta > 0 else True
        geo_ok &= abs(measure - 2 * beta) < 2 * mp.pi / N * 6
        geo_rows.append(dict(rho=str(rho), e=mp.nstr(mf(e), 6), l=mp.nstr(l, 10),
                             beta_rad=mp.nstr(beta, 10), beta_deg=mp.nstr(mp.degrees(beta), 8),
                             cap_measure=mp.nstr(measure, 10),
                             two_beta=mp.nstr(2 * beta, 10)))
    chk["beta_formula_matches_bruteforce_geometry"] = bool(geo_ok)
    rep["geometry_rows"] = geo_rows

    # (c) the cut: ell >= R+U  <=>  qb >= 1  <=> beta = 0
    cut_ok = True
    for l in [F(2, 5), F(1, 2), R + U, R + U + F(1, 100)]:
        qb = (R * R + l * l - U * U) / (2 * R * l)
        cut_ok &= ((qb >= 1) == (l >= R + U))
    chk["cut_ell_ge_R_plus_U_iff_beta_zero"] = bool(cut_ok)
    # (d) beta non-monotone: d qb/d l changes sign at l = sqrt(R^2-U^2)
    lstar = mp.sqrt(mf(R) ** 2 - mf(U) ** 2)
    rep["l_star"] = mp.nstr(lstar, 12)
    f = lambda x: (mf(R) ** 2 + x * x - mf(U) ** 2) / (2 * mf(R) * x)
    nonmono = (f(lstar * mp.mpf('0.5')) > f(lstar)) and (f(lstar * mp.mpf('2')) > f(lstar))
    chk["qb_non_monotone_in_l_so_direct_expression_needed"] = bool(nonmono)

    # ---------- Part II: independent cover on requested segments ----------
    idxs = [int(a) for a in sys.argv[1:]] if len(sys.argv) > 1 else []
    rows = []
    for i in idxs:
        s = segs[i]
        wb = tuple(F(x) for x in s["weights"]["boundary"])
        wh = tuple(F(x) for x in s["weights"]["hub"])
        qA, qB = (F(x) for x in s["e_fraction"])
        r = cover((wb, wh), qA, qB, 10, 10)
        rec_lo, rec_hi = [F(x) for x in s["upper"].strip("[]").split(",")]
        r.update(segment=i, recorded_upper_hi=str(rec_hi), i_agree=bool(F(r["worst"]) >= rec_hi - F(1, 10 ** 10)))
        rows.append(r)
    rep["cover_rows"] = rows
    rep["checks"] = {k: v for k, v in chk.items()}
    (OUT / "nearmerge-audit.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False,
                                                        default=str), encoding="utf-8")
    for k, v in chk.items():
        print("%s  %s" % ("PASS" if v else "FAIL", k))
    print("log ->", OUT / "nearmerge-audit.json")
    if any(v is False for v in chk.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
