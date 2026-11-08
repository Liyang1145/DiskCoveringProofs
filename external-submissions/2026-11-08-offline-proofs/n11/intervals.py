"""Outward-rounded interval arithmetic using only Python integers."""

from fractions import Fraction
from math import isqrt


class Interval:
    SCALE = 1 << 160
    __slots__ = ("lo", "hi")

    def __init__(self, left, right=None):
        a = Fraction(left) * self.SCALE
        b = a if right is None else Fraction(right) * self.SCALE
        self.lo = a.numerator // a.denominator
        self.hi = -(-b.numerator // b.denominator)
        assert self.lo <= self.hi

    @classmethod
    def raw(cls, lo, hi):
        assert lo <= hi
        result = object.__new__(cls)
        result.lo, result.hi = lo, hi
        return result

    @classmethod
    def get(cls, value):
        if isinstance(value, cls):
            return value
        return cls(value)

    def __neg__(self):
        return self.raw(-self.hi, -self.lo)

    def __add__(self, other):
        other = self.get(other)
        return self.raw(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __sub__(self, other):
        other = self.get(other)
        return self.raw(self.lo - other.hi, self.hi - other.lo)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = self.get(other)
        ends = (self.lo * other.lo, self.lo * other.hi,
                self.hi * other.lo, self.hi * other.hi)
        return self.raw(min(ends) // self.SCALE, -(-max(ends) // self.SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.get(other)
        assert other.lo > 0 or other.hi < 0, "division across zero"
        reciprocal = self.raw(self.SCALE**2 // other.hi,
                              -(-self.SCALE**2 // other.lo))
        return self * reciprocal

    def __rtruediv__(self, other):
        return self.get(other) / self

    def square(self):
        a, b = self.lo * self.lo, self.hi * self.hi
        lo = 0 if self.lo <= 0 <= self.hi else min(a, b)
        return self.raw(lo // self.SCALE, -(-max(a, b) // self.SCALE))

    def sqrt(self):
        assert self.lo >= 0, "square root of a negative interval"
        lo = isqrt(self.lo * self.SCALE)
        hi = isqrt(self.hi * self.SCALE)
        return self.raw(lo, hi + (hi * hi < self.hi * self.SCALE))

    def clamp(self, lo, hi):
        return self.raw(max(lo.lo, min(hi.lo, self.lo)),
                        max(lo.hi, min(hi.hi, self.hi)))

    def nonnegative(self):
        return self.raw(max(0, self.lo), max(0, self.hi))

    def mid(self):
        return Fraction((self.lo + self.hi) // 2, self.SCALE)

    def abs_upper(self):
        return max(abs(self.lo), abs(self.hi))

    def split(self):
        mid = (self.lo + self.hi) // 2
        assert self.lo < mid < self.hi
        return self.raw(self.lo, mid), self.raw(mid, self.hi)

    def __repr__(self):
        return f"[{self.lo / self.SCALE:.17g}, {self.hi / self.SCALE:.17g}]"
