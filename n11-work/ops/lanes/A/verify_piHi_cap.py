#!/usr/bin/env python3
"""Exact check of the single q0 degree-three piHi cap inequality.

Expands the 15-term rational Taylor bracket used by `sinHiNLag` and includes
the positive degree-29 Lagrange remainder.  This audits rational data only; the
Lean theorem `SevenClassQ0Deg3Bins.piHiCapSaturated` remains CI-pending.
"""
from fractions import Fraction
from math import factorial

PI_HI = Fraction(314159265358979323847, 10**20)


def sin_tq14(x: Fraction) -> Fraction:
    return sum(((-1) ** k) * x ** (2 * k + 1) / factorial(2 * k + 1)
               for k in range(15))


x = PI_HI / 2
bracket = sin_tq14(x) + x ** 29 / factorial(29)
slack = bracket - 1
assert slack > 0, slack
assert PI_HI > 0
print(f"piHi/2              = {float(x):.17g}")
print(f"sinHiNLag(piHi/2)-1 = {float(slack):.17g} (positive)")
print(f"exact slack numerator bits / denominator bits = "
      f"{slack.numerator.bit_length()} / {slack.denominator.bit_length()}")
