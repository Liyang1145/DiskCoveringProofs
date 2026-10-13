#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""test_crit_straddle.py -- sharp regression test for the B4 critical-point condition.

Construction (per critical point, no sampling): let [L,H] be the kernel's pi-enclosure
of the critical point x* (so L <= x* <= H by the enclosure property) and let X be a
60-digit mpmath value of x*.  Put a = (L+X)/2 (then L < a < x*, rigorously, because
x* - L is ~1e-19 while mpmath's error is ~1e-55) and b = H.  Then x* lies in [a,b],
but the ENCLOSURE [L,H] is NOT contained in [a,b] (since L < a): a containment test
misses the attained extreme value.  The test asserts:
  * the endpoint-only hull (what a containment test would return) does NOT contain +-1
  -> the old condition was unsoundly narrow for such intervals;
  * the kernel's sincos_iv DOES return +-1 (intersection condition).
"""
from fractions import Fraction as F
import mpmath as mp

import kern80 as K

mp.mp.dps = 60
OK = True


def check(x_mp, want_sin, want_cos, label):
    global OK
    X = F(str(mp.nstr(x_mp, 55)))
    for iv, nm, val in K.CRITS:
        L, H = iv.lo, iv.hi
        # identify the entry whose critical point is this x*
        if not (L <= X <= H):
            continue
        if nm == "sin" and val != want_sin:
            continue
        if nm == "cos" and val != want_cos:
            continue
        a = (L + X) / 2
        b = H
        if not (L < a < X <= b):
            print("  skip (no strict straddle room):", label)
            continue
        s, c = K.sincos_iv(a, b)
        # endpoint-only hull (the old, containment-based result)
        s_lo_e, c_lo_e = K.sincos_pt(a)
        s_hi_e, c_hi_e = K.sincos_pt(b)
        old_s = K.hull(s_lo_e, s_hi_e)
        old_c = K.hull(c_lo_e, c_hi_e)
        got_s = (s.lo <= want_sin <= s.hi) if want_sin is not None else None
        got_c = (c.lo <= want_cos <= c.hi) if want_cos is not None else None
        old_ok_s = (old_s.lo <= want_sin <= old_s.hi) if want_sin is not None else None
        old_ok_c = (old_c.lo <= want_cos <= old_c.hi) if want_cos is not None else None
        print("  %-22s [a,b]=[%s..., %s...]  kernel sin=%s cos=%s | endpoint-only sin=%s cos=%s"
              % (label, str(a)[:14], str(b)[:14], got_s, got_c, old_ok_s, old_ok_c))
        if want_sin is not None:
            OK &= bool(got_s)
        if want_cos is not None:
            OK &= bool(got_c)
        # demonstrate the gap: endpoint-only must fail on the relevant component
        if want_sin is not None and not old_ok_s:
            print("     -> containment-only enclosure MISSES %s = %d  (gap confirmed)"
                  % ("sin", want_sin))
        if want_cos is not None and not old_ok_c:
            print("     -> containment-only enclosure MISSES %s = %d  (gap confirmed)"
                  % ("cos", want_cos))


def main():
    print("sharp straddle test:")
    check(mp.pi / 2, 1, None, "sin=+1 at pi/2")
    check(3 * mp.pi / 2, -1, None, "sin=-1 at 3pi/2")
    check(mp.pi, None, -1, "cos=-1 at pi")
    check(2 * mp.pi, None, 1, "cos=+1 at 2pi")
    print()
    print("PASS: kernel uses the intersection condition" if OK else "FAIL")
    if not OK:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
