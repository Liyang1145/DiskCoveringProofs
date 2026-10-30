#!/usr/bin/env python3
"""Exact margin audit for a non-expansion proof of the piHi cap.

The intended Lean proof uses `sinHiNLag q = sinT 15 q`, the Taylor-16
remainder bound, `sin x >= 1 - d^2/2` at `x = piHi/2 = pi/2 + d`, and
`d < 1/(2*10^20)`.  This script checks the resulting rational margin.
"""
from fractions import Fraction
from math import factorial

lo = Fraction(3, 2)
hi = Fraction(1571, 1000)
margin = lo**31 / factorial(31) - hi**33 / factorial(33)
required = Fraction(1, 8 * 10**40)
assert margin > required, (margin, required)
print(f"Taylor-31 lower term = {float(margin):.17g}")
print(f"cos-deficit allowance = {float(required):.17g}")
print(f"slack ratio           = {float(margin / required):.3g}")
print("PASS: analytic cap margin is positive")
