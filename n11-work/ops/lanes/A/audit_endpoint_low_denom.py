#!/usr/bin/env python3
"""Check low-denominator upper bounds for the eight endpoint comparisons.

For bins 0--4, q/2 is bounded above by uBin[j] <= 1 and the degree-seven
polynomial is increasing on [0,1].  Bins 5--6 need the degree-nine and
degree-29 Taylor remainders kept explicitly because their arguments exceed 1.
Bin 7 uses the separately proved saturation `capQ piHi = 19/50`; guessing a
degree-seven upper bound outside [0,1] would not be sound.  All arithmetic is
exact Fraction arithmetic; this is candidate data, not kernel evidence.
"""

from fractions import Fraction
from math import factorial


PI_HI = Fraction(314159265358979323847, 10**20)
U_BIN = [
    Fraction(1956, 10000),
    Fraction(3920, 10000),
    Fraction(5883, 10000),
    Fraction(7847, 10000),
    Fraction(9810, 10000),
    Fraction(11774, 10000),
    Fraction(13737, 10000),
    Fraction(15708, 10000),
]
NODE_BIN = [
    Fraction(239, 1250),
    Fraction(239, 1250),
    Fraction(133, 625),
    Fraction(2721, 10000),
    Fraction(643, 2000),
    Fraction(897, 2500),
    Fraction(191, 500),
    Fraction(1949, 5000),
]


def sin_poly4(x: Fraction) -> Fraction:
    return x - x**3 / 6 + x**5 / 120 - x**7 / 5040


def sin_hi_upper_pow(x: Fraction) -> Fraction:
    return (sin_poly4(x) + abs(x) ** 9 / factorial(9) +
            2 * abs(x) ** 29 / factorial(29))


def main() -> int:
    eps = Fraction(1, factorial(9)) + 2 * Fraction(1, factorial(29))
    failures = 0
    for j, (u, a) in enumerate(zip(U_BIN, NODE_BIN)):
        q = PI_HI * (2048 if j == 7 else 256 * j + 255) / 2048
        q_le_u = q / 2 <= u
        if j <= 4:
            branch = "poly4/u"
            upper = Fraction(19, 50) * max(
                Fraction(1, 2), min(Fraction(1), sin_poly4(u) + eps)
            )
        elif j <= 6:
            branch = "poly4+remainders"
            y = sin_hi_upper_pow(q / 2)
            upper = Fraction(19, 50) * y
        else:
            branch = "saturated"
            upper = Fraction(19, 50)
        lower = sin_poly4(a) - eps
        branch_ok = (j == 7) or q_le_u
        if 5 <= j <= 6:
            branch_ok = branch_ok and sin_hi_upper_pow(q / 2) >= Fraction(1, 2)
        ok = branch_ok and upper <= lower
        failures += not ok
        print(
            f"bin {j} [{branch}]: q/2 <= {u}: {q_le_u}; "
            f"slack={float(lower - upper):.12g}; {'PASS' if ok else 'FAIL'}"
        )
    print(f"FAILURES: {failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
