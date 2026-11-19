"""Outward rounded real intervals on a dyadic grid, with first derivatives."""
from fractions import Fraction
from math import isqrt

Q = 2**168


def ceildiv(x, y):
    return -((-x)//y)


class I:
    __slots__ = ("lo", "hi")

    @classmethod
    def raw(cls, lo, hi):
        assert lo <= hi
        value = object.__new__(cls)
        value.lo, value.hi = lo, hi
        return value

    def __init__(self, x):
        if isinstance(x, I):
            self.lo, self.hi = x.lo, x.hi
        else:
            q = Fraction(x)
            self.lo = q.numerator * Q // q.denominator
            self.hi = ceildiv(q.numerator * Q, q.denominator)

    def __neg__(self):
        return I.raw(-self.hi, -self.lo)

    def __add__(self, y):
        if isinstance(y, AD):
            return NotImplemented
        y = I(y)
        return I.raw(self.lo + y.lo, self.hi + y.hi)

    __radd__ = __add__

    def __sub__(self, y):
        if isinstance(y, AD):
            return NotImplemented
        return self + -I(y)

    def __rsub__(self, y):
        return I(y) + -self

    def __mul__(self, y):
        if isinstance(y, AD):
            return NotImplemented
        y = I(y)
        ends = [self.lo*y.lo, self.lo*y.hi, self.hi*y.lo, self.hi*y.hi]
        return I.raw(min(ends)//Q, ceildiv(max(ends), Q))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return I.raw(Q*Q//self.hi, ceildiv(Q*Q, self.lo))

    def __truediv__(self, y):
        if isinstance(y, AD):
            return NotImplemented
        return self * I(y).reciprocal()

    def __rtruediv__(self, y):
        return I(y) * self.reciprocal()

    def sqrt(self):
        assert self.lo >= 0
        return I.raw(isqrt(self.lo*Q), isqrt(self.hi*Q)+1)

    def maximum_abs(self):
        return max(abs(self.lo), abs(self.hi))

    def midpoint(self):
        return Fraction(self.lo+self.hi, 2*Q)


def hull(x, rad):
    x, rad = I(x), I(rad)
    return I.raw(x.lo-rad.hi, x.hi+rad.hi)


class AD:
    __slots__ = ("v", "d")

    def __init__(self, value, derivatives=None):
        self.v = I(value)
        self.d = [I(0), I(0), I(0)] if derivatives is None else derivatives

    @classmethod
    def variable(cls, x, index):
        return cls(x, [I(k==index) for k in range(3)])

    def __neg__(self):
        return AD(-self.v, [-x for x in self.d])

    def __add__(self, other):
        y = ad(other)
        return AD(self.v+y.v, [x+z for x,z in zip(self.d,y.d)])

    __radd__ = __add__

    def __sub__(self, other):
        return self + -ad(other)

    def __rsub__(self, other):
        return ad(other) + -self

    def __mul__(self, other):
        y = ad(other)
        return AD(self.v*y.v, [x*y.v+self.v*z for x,z in zip(self.d,y.d)])

    __rmul__ = __mul__

    def __truediv__(self, other):
        y = ad(other)
        value = self.v/y.v
        return AD(value, [(x-value*z)/y.v for x,z in zip(self.d,y.d)])

    def __rtruediv__(self, other):
        return ad(other) / self

    def sqrt(self):
        value = self.v.sqrt()
        return AD(value, [x/(2*value) for x in self.d])


def ad(x):
    return x if isinstance(x, AD) else AD(x)


def midpoint_inverse(matrix):
    m = [[x.midpoint() for x in row]+[Fraction(i==j) for j in range(3)]
         for i,row in enumerate(matrix)]
    for i in range(3):
        k = next(k for k in range(i,3) if m[k][i])
        m[i],m[k]=m[k],m[i]
        d=m[i][i]
        m[i] = [x/d for x in m[i]]
        for k in range(3):
            if k != i:
                x = m[k][i]
                m[k]=[u-x*v for u,v in zip(m[k],m[i])]
    return [row[3:] for row in m]
