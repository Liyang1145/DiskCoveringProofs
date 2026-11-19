from math import factorial, isqrt


SCALE = 10**34


def ceil_div(a, b):
    return -((-a) // b)


class Interval:
    """An interval whose two endpoints are integers in units of 10^-34."""

    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi):
        if lo > hi:
            raise ValueError('empty interval')
        self.lo = lo
        self.hi = hi

    @classmethod
    def ratio(cls, n, d=1):
        return cls(n * SCALE // d, ceil_div(n * SCALE, d))

    @classmethod
    def decimal(cls, source):
        before, _, after = source.partition('.')
        numerator = int(before + after)
        return cls.ratio(numerator, 10**len(after))

    @classmethod
    def cast(cls, x):
        return x if isinstance(x, cls) else cls.ratio(x)

    def __add__(self, other):
        b = self.cast(other)
        return Interval(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) + (-self)

    def __mul__(self, other):
        b = self.cast(other)
        products = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return Interval(min(products) // SCALE, ceil_div(max(products), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.cast(other)
        if b.lo <= 0 <= b.hi:
            raise ZeroDivisionError('interval contains zero')
        inverse = Interval(SCALE**2 // b.hi, ceil_div(SCALE**2, b.lo))
        return self * inverse

    def __rtruediv__(self, other):
        return self.cast(other) / self

    def square(self):
        a, b = self.lo**2, self.hi**2
        lower = 0 if self.lo <= 0 <= self.hi else min(a, b)
        return Interval(lower // SCALE, ceil_div(max(a, b), SCALE))

    def sqrt(self):
        a = isqrt(self.lo*SCALE)
        b = isqrt(self.hi*SCALE)
        return Interval(a, b + (b*b < self.hi*SCALE))

    def absupper(self):
        return max(abs(self.lo), abs(self.hi))

    def mid(self):
        v = (self.lo + self.hi) // 2
        return Interval(v, v)

    def __repr__(self):
        return f'[{self.lo}/{SCALE}, {self.hi}/{SCALE}]'


Q = Interval.ratio
D = Interval.decimal
ZERO = Q(0)
ONE = Q(1)


def atan_inverse(q):
    terms = 30
    partial = sum(Q((-1)**j, (2*j+1)*q**(2*j+1)) for j in range(terms))
    tail = Q(1, (2*terms+1)*q**(2*terms+1))
    return Interval(partial.lo-tail.hi, partial.hi+tail.hi)


PI = 16*atan_inverse(5) - 4*atan_inverse(239)


def trig(x, sine):
    """Taylor polynomial plus its Lagrange remainder, for |x| <= 4."""
    if x.absupper() > 4*SCALE:
        raise ValueError('angle outside Taylor range')
    term = x if sine else ONE
    squared = -x.square()
    partial = term
    for j in range(1, 27):
        n = 2*j+int(sine)
        term = term * squared / (n*(n-1))
        partial += term
    n = 53+int(sine)
    error = ceil_div(SCALE*4**n, factorial(n))
    return Interval(partial.lo-error, partial.hi+error)


def cos(x):
    return trig(x, False)


def sin(x):
    return trig(x, True)


class Jet:
    """An interval enclosure of a function and its first two derivatives."""

    def __init__(self, value, gradient=(ZERO,ZERO), second=((ZERO,ZERO),(ZERO,ZERO))):
        self.v = Interval.cast(value)
        self.g = gradient
        self.h = second

    @classmethod
    def var(cls, value, index):
        return cls(value, tuple(Q(j == index) for j in range(2)))

    @classmethod
    def cast(cls, value):
        return value if isinstance(value, cls) else cls(value)

    def __add__(self, other):
        b = self.cast(other)
        return Jet(self.v+b.v,
                   tuple(self.g[i]+b.g[i] for i in range(2)),
                   tuple(tuple(self.h[i][j]+b.h[i][j] for j in range(2)) for i in range(2)))

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, tuple(-v for v in self.g), tuple(tuple(-v for v in row) for row in self.h))

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) + (-self)

    def __mul__(self, other):
        b = self.cast(other)
        return Jet(self.v*b.v,
                   tuple(self.g[i]*b.v+self.v*b.g[i] for i in range(2)),
                   tuple(tuple(self.h[i][j]*b.v + self.g[i]*b.g[j] + self.g[j]*b.g[i] + self.v*b.h[i][j]
                               for j in range(2)) for i in range(2)))

    __rmul__ = __mul__

    def __truediv__(self, n):
        return self * Q(1,n)

    def sqrt(self):
        value = self.v.sqrt()
        d = 1/(2*value)
        dd = -1/(4*self.v*value)
        return Jet(value,
                   tuple(d*u for u in self.g),
                   tuple(tuple(dd*self.g[i]*self.g[j] + d*self.h[i][j] for j in range(2)) for i in range(2)))
