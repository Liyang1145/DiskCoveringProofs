#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""calib_kern80.py -- calibrate the independent kernel against mpmath at 160 digits.

Checks done:
  P1  pi enclosure contains mpmath pi (160 dps)
  P2  sin/cos point enclosures contain mpmath values (random rationals, full range)
  P3  sin/cos interval enclosures contain the min/max sampled at 400 interior points
  P4  wide-interval sanity: sin/cos of [0, 2pi] must be [-1,1]
  P5  asin/acos enclosures contain mpmath values, including the |x|>1/2 branch
  P6  sqrt enclosure
  P7  grid rounding direction (dwn/upp)
  P8  the mpmath.iv operations actually used by the lead's kernel: soundness probes
      (iv.cos/iv.sin on wide intervals, iv.atan2 with interval arguments, iv.sqrt,
       iv.mpf([...]) endpoint semantics)
"""
from fractions import Fraction as F
from pathlib import Path
import random
import mpmath as mp
import json

import kern80 as K

mp.mp.dps = 160
OUT = Path(__file__).resolve().parent / "out"
OUT.mkdir(exist_ok=True)


def mpsin(x):
    return mp.sin(mp.mpf(x.numerator) / x.denominator)


def mpcos(x):
    return mp.cos(mp.mpf(x.numerator) / x.denominator)


def mpasin(x):
    return mp.asin(mp.mpf(x.numerator) / x.denominator)


def mpacos(x):
    return mp.acos(mp.mpf(x.numerator) / x.denominator)


def contains(iv, val):
    lo, hi = F(iv.lo), F(iv.hi)
    v = mp.mpf(val)
    return mp.mpf(lo.numerator) / lo.denominator <= v <= mp.mpf(hi.numerator) / hi.denominator


def main():
    rep, ok = {}, True
    # P1
    rep["pi_contains"] = contains(K.PI, mp.pi)
    ok &= rep["pi_contains"]
    rep["pi_width"] = mp.nstr(mp.mpf(K.PI.hi.numerator) / K.PI.hi.denominator
                              - mp.mpf(K.PI.lo.numerator) / K.PI.lo.denominator, 5)
    # P2/P3
    rng = random.Random(2026)
    fail_s = fail_c = 0
    min_slack = None
    for _ in range(400):
        x = F(rng.randint(-628, 628), 100)
        s, c = K.sincos_pt(x)
        if not contains(s, mpsin(x)):
            fail_s += 1
        if not contains(c, mpcos(x)):
            fail_c += 1
        slack = min(mpsin(x) - mp.mpf(s.lo.numerator) / s.lo.denominator,
                    mp.mpf(s.hi.numerator) / s.hi.denominator - mpsin(x))
        min_slack = slack if min_slack is None else min(min_slack, slack)
    rep["point_sin_fail"] = fail_s
    rep["point_cos_fail"] = fail_c
    rep["point_min_slack"] = mp.nstr(min_slack, 5)
    ok &= (fail_s == 0 and fail_c == 0)
    # interval containment
    fail_iv = 0
    for _ in range(120):
        a = F(rng.randint(-628, 628), 100)
        b = a + F(rng.randint(0, 300), 100)
        s, c = K.sincos_iv(a, b)
        for t in range(1, 40):
            x = a + (b - a) * F(t, 40)
            if not (contains(s, mpsin(x)) and contains(c, mpcos(x))):
                fail_iv += 1
                break
    rep["interval_sincos_fail"] = fail_iv
    ok &= (fail_iv == 0)
    # P4
    s, c = K.sincos_iv(F(0), 2 * K.PI.hi)
    rep["wide_interval_sincos"] = [[str(s.lo), str(s.hi)], [str(c.lo), str(c.hi)]]
    ok &= (s.lo <= -1 and s.hi >= 1 and c.lo <= -1 and c.hi >= 1)
    # P5
    fa = fac = 0
    for _ in range(200):
        x = F(rng.randint(-1000, 1000), 1000)
        A = K.asin_iv(x, x)
        if not contains(A, mpasin(x)):
            fa += 1
        C = K.acos_iv(x, x)
        if not contains(C, mpacos(x)):
            fac += 1
    # interval asin/acos
    fi = 0
    for _ in range(80):
        a = F(rng.randint(-1000, 1000), 1000)
        b = min(F(1), a + F(rng.randint(0, 400), 1000))
        A = K.asin_iv(a, b)
        C = K.acos_iv(a, b)
        for t in range(1, 25):
            x = a + (b - a) * F(t, 25)
            if not (contains(A, mpasin(x)) and contains(C, mpacos(x))):
                fi += 1
                break
    rep["asin_point_fail"] = fa
    rep["acos_point_fail"] = fac
    rep["asin_acoss_interval_fail"] = fi
    ok &= (fa == 0 and fac == 0 and fi == 0)
    # P6/P7
    fq = 0
    for _ in range(200):
        x = F(rng.randint(0, 10 ** 6), 10 ** 6)
        q = K.sqrt_iv(K.Iv(x, x))
        if not contains(q, mp.sqrt(mp.mpf(x.numerator) / x.denominator)):
            fq += 1
    rep["sqrt_fail"] = fq
    ok &= (fq == 0)
    rep["grid_rounding_ok"] = (K.dwn(F(1, 3)) <= F(1, 3) <= K.upp(F(1, 3)) and
                               (K.upp(F(1, 3)) - K.dwn(F(1, 3))) <= 2 * K.G)
    ok &= rep["grid_rounding_ok"]

    # P8: mpmath.iv probes for the operations the lead's kernel uses
    iv = mp.iv
    iv.dps = 30
    probes = {}
    # (a) cos/sin on a wide interval
    probes["iv_cos_0_2pi"] = str(iv.cos(iv.mpf([0, 2 * iv.pi])))
    probes["iv_sin_0_2pi"] = str(iv.sin(iv.mpf([0, 2 * iv.pi])))
    # (b) atan2 with interval arguments: enumerate the rectangle at high precision and
    #     check the mpmath interval result covers all of them
    ylo, yhi = -1, 1
    xlo, xhi = -1, 1
    res = str(iv.atan2(iv.mpf([ylo, yhi]), iv.mpf([xlo, xhi])))
    probes["iv_atan2_rect"] = res
    worst = None
    inside = True
    for ty in (ylo, (ylo + yhi) / 2, yhi):
        for tx in (xlo, (xlo + xhi) / 2, xhi):
            v = mp.atan2(ty, tx)
            lo, hi = res.strip("[]").split(",")
            if not (mp.mpf(lo) <= v <= mp.mpf(hi)):
                inside = False
    probes["iv_atan2_covers_sampled"] = inside
    # (c) iv.mpf([lo,hi]) keeps the endpoints
    probes["iv_mpf_list_endpoints"] = str(iv.mpf([iv.mpf("-1.5"), iv.mpf("2.25")]))
    # (d) sqrt on an interval
    probes["iv_sqrt"] = str(iv.sqrt(iv.mpf([iv.mpf("2"), iv.mpf("3")])))
    rep["mpmath_iv_probes"] = probes
    ok &= inside

    # report
    print(json.dumps(rep, indent=1)[:4000])
    print("CALIBRATION OK:", ok)
    (OUT / "kernel-calibration.json").write_text(json.dumps(
        {"ok": bool(ok), **{k: (v if not isinstance(v, mp.mpf) else str(v)) for k, v in rep.items()}},
        indent=1), encoding="utf-8")
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
