"""Small exact rational enclosures used by the lower-bound certificates."""

from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, isqrt


def atan_bounds(x, terms):
    lower = sum(
        ((-1) ** j * x ** (2 * j + 1) / (2 * j + 1) for j in range(terms)),
        Q(0),
    )
    next_term = x ** (2 * terms + 1) / (2 * terms + 1)
    return (lower, lower + next_term) if terms % 2 == 0 else (lower - next_term, lower)


@lru_cache
def pi_bounds():
    # Machin's identity and two alternating-series enclosures.
    a, b = atan_bounds(Q(1, 5), 20)
    c, d = atan_bounds(Q(1, 239), 8)
    return 16 * a - 4 * d, 16 * b - 4 * c


def sin_lower(x):
    return sum(((-1) ** j * x ** (2 * j + 1) / factorial(2 * j + 1)
                for j in range(10)), Q(0))


def sin_upper(x):
    return sin_lower(x) + x**21 / factorial(21)


def cos_lower(x):
    return sum(((-1) ** j * x ** (2 * j) / factorial(2 * j) for j in range(10)), Q(0))


def cos_upper(x):
    return cos_lower(x) + x**20 / factorial(20)


def sqrt_bounds(x, scale=10**12):
    numerator = x.numerator * scale * scale
    root = isqrt(numerator // x.denominator)
    return Q(root, scale), Q(root + 1, scale)
