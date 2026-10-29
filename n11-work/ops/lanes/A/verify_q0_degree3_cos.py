#!/usr/bin/env python3
"""Exact-rational audit of the q0 degree-three cosine grid bracket.

This mirrors the frozen `cosTQ 14`, `cosHiNLag`, and `nodeQ` definitions with
Python `Fraction`s. It is candidate-data checking only, not a Lean/kernel claim.
"""

from fractions import Fraction
from math import factorial


PI_LO = Fraction(314159265358979323846, 10**20)
PI_HI = Fraction(314159265358979323847, 10**20)
GRID = 2048


def cos_tq(q: Fraction) -> Fraction:
    return sum(
        ((-1) ** k) * q ** (2 * k) / factorial(2 * k) for k in range(14)
    )


def cos_hi(q: Fraction) -> Fraction:
    return cos_tq(q) + abs(q) ** 28 / factorial(28)


def grid_arg(i: int) -> Fraction:
    return PI_HI * i / GRID / 2


def main() -> None:
    # Rational comparison placing the penultimate node below pi/2.
    assert 2047 * PI_HI <= 2048 * PI_LO
    assert grid_arg(2047) <= PI_LO / 2

    previous = cos_hi(grid_arg(0))
    for i in range(1, GRID + 1):
        current = cos_hi(grid_arg(i))
        assert current <= previous, f"grid inequality fails at step {i}"
        previous = current

    gap = cos_hi(grid_arg(GRID - 1)) - cos_hi(grid_arg(GRID))
    assert gap > 0
    print(f"PASS: exact cosHiNLag antitone on {GRID} adjacent grid steps")
    print(f"PASS: final-step rational gap = {gap}")
    print("scope: candidate rational data only; no Lean/kernel claim")


if __name__ == "__main__":
    main()
