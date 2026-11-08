"""Outward-rounded fixed-point intervals. Uses Python integers only."""

from fractions import Fraction
from math import isqrt


PLACES = 60
SCALE = 10**PLACES


def ceil_div(numerator, denominator):
    assert denominator > 0
    return -(-numerator // denominator)


class Interval:
    def __init__(self, lower, upper=None):
        lo = Fraction(lower)
        hi = lo if upper is None else Fraction(upper)
        assert lo <= hi
        self.lo = lo.numerator * SCALE // lo.denominator
        self.hi = ceil_div(hi.numerator * SCALE, hi.denominator)

    @classmethod
    def endpoints(cls, lo, hi):
        assert lo <= hi
        out = object.__new__(cls)
        out.lo, out.hi = lo, hi
        return out

    @classmethod
    def coerce(cls, value):
        if isinstance(value, cls):
            return value
        if isinstance(value, (int, str, Fraction)):
            return cls(value)
        return NotImplemented

    def __repr__(self):
        def digits(v):
            prefix = "-" if v < 0 else ""
            whole, frac = divmod(abs(v), SCALE)
            return f"{prefix}{whole}.{frac:0{PLACES}d}"

        return f"[{digits(self.lo)}, {digits(self.hi)}]"

    def midpoint(self):
        mid = (self.lo + self.hi) // 2
        return self.endpoints(mid, mid)

    def __neg__(self):
        return self.endpoints(-self.hi, -self.lo)

    def __add__(self, other):
        other = self.coerce(other)
        if other is NotImplemented:
            return NotImplemented
        return self.endpoints(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __sub__(self, other):
        other = self.coerce(other)
        if other is NotImplemented:
            return NotImplemented
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = self.coerce(other)
        if other is NotImplemented:
            return NotImplemented
        products = (self.lo * other.lo, self.lo * other.hi,
                    self.hi * other.lo, self.hi * other.hi)
        return self.endpoints(min(products) // SCALE, ceil_div(max(products), SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.hi < 0:
            return -(-self).reciprocal()
        assert self.lo > 0
        return self.endpoints(SCALE * SCALE // self.hi,
                              ceil_div(SCALE * SCALE, self.lo))

    def __truediv__(self, other):
        other = self.coerce(other)
        if other is NotImplemented:
            return NotImplemented
        return self * other.reciprocal()

    def __rtruediv__(self, other):
        return self.reciprocal() * other

    def square(self):
        low = min(abs(self.lo), abs(self.hi)) if self.lo * self.hi > 0 else 0
        high = max(abs(self.lo), abs(self.hi))
        return self.endpoints(low * low // SCALE, ceil_div(high * high, SCALE))

    def sqrt(self):
        assert self.lo >= 0
        high = self.hi * SCALE
        upper = isqrt(high)
        return self.endpoints(isqrt(self.lo * SCALE), upper + int(upper * upper != high))


def atan(x):
    """Enclose atan(x) for 0 <= x <= 1 by reducing the argument."""
    assert 0 <= x.lo <= x.hi <= SCALE
    for _ in range(2):
        x = x / (1 + (1 + x.square()).sqrt())
    assert x.hi * 4 < SCALE
    x2 = x.square()
    term = x
    total = Interval(0)
    for k in range(30):
        contribution = term / (2*k + 1)
        total = total + contribution if k % 2 == 0 else total - contribution
        term = term * x2
    # The partial sum ends with a negative term, so the remainder is positive.
    remainder = term / 61
    return 4 * (total + Interval.endpoints(0, remainder.hi))


def asin(x):
    assert 0 <= x.lo <= x.hi <= SCALE
    ratio = x / (1 + (1 - x.square()).sqrt())
    # The exact half-angle tangent is at most 1.
    ratio = Interval.endpoints(ratio.lo, min(ratio.hi, SCALE))
    return 2 * atan(ratio)


PI = 4 * atan(Interval(1))
