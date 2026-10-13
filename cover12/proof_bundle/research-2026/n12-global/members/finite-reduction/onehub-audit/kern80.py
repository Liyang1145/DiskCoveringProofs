#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""kern80.py -- self-contained rigorous interval kernel at fixed grid 2**-80.

Independent of mpmath: exact Fractions with OUTWARD rounding to the grid after every
operation; pi from Machin's formula with rational alternating bounds; sin/cos by
argument reduction mod 2*pi (using the pi enclosure) plus halving/doubling and
alternating series brackets; asin/acos by series with an explicit positive tail bound
plus the half-angle reduction for |x|>1/2.

All endpoints are exact multiples of the grid unit g = 2**-80.
"""
from fractions import Fraction as F
import math

BITS = 64
G = F(1, 2 ** BITS)


def dwn(x):
    x = F(x)
    return (x / G).__floor__() * G


def upp(x):
    x = F(x)
    return -((-x / G).__floor__()) * G


def hull(*ivs):
    return Iv(min(v.lo for v in ivs), max(v.hi for v in ivs))


class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if isinstance(lo, Iv) and hi is None:
            self.lo, self.hi = lo.lo, lo.hi
            return
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = dwn(lo), upp(hi)

    def __add__(x, y):
        return Iv(x.lo + y.lo, x.hi + y.hi)

    def __radd__(x, y):
        return Iv(y) + x

    def __neg__(x):
        return Iv(-x.hi, -x.lo)

    def __sub__(x, y):
        return x + (-Iv(y))

    def __rsub__(x, y):
        return Iv(y) + (-x)

    def __mul__(x, y):
        y = Iv(y)
        v = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
        return Iv(min(v), max(v))

    def __rmul__(x, y):
        return x * Iv(y)

    def __truediv__(x, y):
        y = Iv(y)
        if y.lo <= 0 <= y.hi:
            raise ValueError("division by interval containing 0")
        v = [x.lo / y.lo, x.lo / y.hi, x.hi / y.lo, x.hi / y.hi]
        return Iv(min(v), max(v))

    def __rtruediv__(x, y):
        return Iv(y) / x

    def __pow__(x, n):
        assert isinstance(n, int) and n >= 0
        y = Iv(1)
        for _ in range(n):
            y = y * x
        return y

    def pos(x):
        return x.lo > 0

    def nonneg(x):
        return x.lo >= 0

    def contains0(x):
        return x.lo <= 0 <= x.hi

    def overlap(x, y):
        y = Iv(y)
        return not (x.hi < y.lo or y.hi < x.lo)

    def inside(x, y):
        y = Iv(y)
        return y.lo <= x.lo and x.hi <= y.hi

    def dump(x):
        return [str(x.lo), str(x.hi)]

    def loose(x, nd=10):
        return "[%.*g, %.*g]" % (nd, float(x.lo), nd, float(x.hi))

    def __repr__(x):
        return "Iv(%s,%s)" % (x.lo, x.hi)


def sqrt_iv(x):
    """outward sqrt of a nonnegative interval: x = m/2**80 -> sqrt(x) = sqrt(m)/2**40"""
    assert x.lo >= 0, x
    m_lo = int(x.lo * 2 ** BITS)
    m_hi = int(x.hi * 2 ** BITS)
    a = math.isqrt(m_lo)                  # a <= sqrt(m_lo)
    b = math.isqrt(m_hi)
    if b * b < m_hi:
        b += 1                            # b >= sqrt(m_hi)
    return Iv(F(a, 2 ** (BITS // 2)), F(b, 2 ** (BITS // 2)))


# ---------------------------------------------------------------- pi
def pi_iv(terms=70):
    """Machin: pi = 16 atan(1/5) - 4 atan(1/239); alternating rational brackets."""
    def atan_inv(n, k):
        s = F(0)
        sign = 1
        for i in range(k):
            s += sign * F(1, (2 * i + 1) * n ** (2 * i + 1))
            sign = -sign
        rem = F(1, (2 * k + 1) * n ** (2 * k + 1))
        return s - rem, s + rem
    a5lo, a5hi = atan_inv(5, terms)
    a239lo, a239hi = atan_inv(239, terms)
    return Iv(16 * a5lo - 4 * a239hi, 16 * a5hi - 4 * a239lo)


PI = pi_iv()
TWO_PI = Iv(2 * PI.lo, 2 * PI.hi)
HALF_PI = Iv(PI.lo / 2, PI.hi / 2)


# ---------------------------------------------------------------- sin/cos
def _sin_pt_small(x, k=10):
    """sin(x), |x| <= 1/2, alternating series brackets (partial sums bracket the sum).
    Computed for |x| (odd partial sums below, even above) then negated if x < 0."""
    x = F(x)
    assert abs(x) <= F(1, 2), x
    y = abs(x)
    t = F(y)
    S = t
    lo, hi = None, S
    for i in range(1, k + 1):
        t = -t * y * y / ((2 * i) * (2 * i + 1))
        S += t
        if i % 2 == 1:
            lo = S
        else:
            hi = S
    assert lo is not None
    s = Iv(lo, hi)
    return s if x >= 0 else -s


def _cos_pt_small(x, k=10):
    x = F(x)
    assert abs(x) <= F(1, 2), x
    t = F(1)
    S = t
    lo, hi = None, S
    for i in range(1, k + 1):
        t = -t * x * x / ((2 * i - 1) * (2 * i))
        S += t
        if i % 2 == 1:
            lo = S
        else:
            hi = S
    assert lo is not None
    return Iv(lo, hi)


def sincos_pt(x):
    """(sin, cos) enclosure at a point x (|x| <= 2*pi + 1) by halving then doubling"""
    x = F(x)
    k = 0
    y = x
    while abs(y) > F(1, 2):
        y = y / 2
        k += 1
    s = _sin_pt_small(y)
    c = _cos_pt_small(y)
    for _ in range(k):
        s, c = 2 * s * c, c * c - s * s
    return s, c


def _crit_contains(a, b, off, step):
    """do the points (off + k*step)*pi for integer k cover an entire [v_lo,v_hi] inside
    [a,b]?  (used to certify attainment of +-1 inside the interval)"""
    k_lo = ((a / PI.hi) - off) / step - 2
    k_hi = ((b / PI.lo) - off) / step + 2
    for k in range(int(k_lo.__floor__()), int(k_hi.__ceil__()) + 1):
        c = F(off) + k * step
        v_lo, v_hi = (c * PI.lo, c * PI.hi) if c >= 0 else (c * PI.hi, c * PI.lo)
        if v_lo >= a and v_hi <= b:
            return True
    return False


def _crit_table():
    """enclosures of every point in [-7,7] where sin or cos attains +-1, with the value"""
    tab = []
    for off, val, nm in ((F(1, 2), 1, "sin"), (F(3, 2), -1, "sin"),
                         (F(0), 1, "cos"), (F(1), -1, "cos")):
        for k in range(-7, 8):
            c = off + 2 * k
            lo, hi = (c * PI.lo, c * PI.hi) if c >= 0 else (c * PI.hi, c * PI.lo)
            if hi < -13 or lo > 13:
                continue
            tab.append((Iv(lo, hi), nm, val))
    return tab


CRITS = _crit_table()

# instrumentation (no effect on values): how often does a critical-point enclosure
# straddle an endpoint of [a,b]?  That is exactly the case in which a containment-only
# test would have missed the attained extreme value.
GAP_STATS = {"calls": 0, "fires": 0, "straddle": 0}


def sincos_iv(a, b):
    """rigorous (sin, cos) enclosure for the interval [a, b]

    Critical points: +-1 is inserted whenever the pi-ENCLOSURE of a critical point
    INTERSECTS [a,b] (not only when it is contained in [a,b]).  If the true critical
    point lies in [a,b] while its enclosure straddles an endpoint, a containment test
    misses the attained extreme value and the endpoint values need not cover it, i.e.
    the enclosure would be unsoundly narrow.  Intersection may over-include values
    that are not attained, which is always safe (it only widens the bound)."""
    a, b = F(a), F(b)
    assert a <= b
    if b - a >= TWO_PI.hi:                       # a whole period is contained
        return Iv(-1, 1), Iv(-1, 1)
    s_lo, c_lo = sincos_pt(a)
    s_hi, c_hi = sincos_pt(b)
    sv = [s_lo, s_hi]
    cv = [c_lo, c_hi]
    GAP_STATS["calls"] += 1
    for iv, nm, val in CRITS:                    # enclosure intersects [a,b]?
        if iv.hi >= a and iv.lo <= b:
            GAP_STATS["fires"] += 1
            if not (a <= iv.lo and iv.hi <= b):
                GAP_STATS["straddle"] += 1
            (sv if nm == "sin" else cv).append(Iv(val, val))
    return hull(*sv), hull(*cv)


# ---------------------------------------------------------------- asin / acos
def _asin_series_iv(a, b, N=24):
    """asin on [a,b] with |x| <= 9/10: all series coefficients positive and <= 1/2, so
    partial sums are lower bounds and partial + tail(|x|^{2N+3}/(2(1-x^2))) upper bounds."""
    def one(x):
        x = F(x)
        assert abs(x) <= F(9, 10), x
        s = F(0)
        c = F(1)
        term = F(x)
        s += term
        for k in range(1, N + 1):
            c = c * F((2 * k - 1) ** 2, (2 * k) * (2 * k + 1))
            term = c * x ** (2 * k + 1)
            s += term
        tail = abs(x) ** (2 * N + 3) / (2 * (1 - x * x))
        return Iv(s, s + tail) if x >= 0 else Iv(s - tail, s)
    if a >= 0:
        return Iv(one(a).lo, one(b).hi)
    if b <= 0:
        return Iv(one(a).lo, one(b).hi)
    return hull(one(a), one(b))


def asin_iv(a, b):
    a, b = F(a), F(b)
    assert -1 <= a <= b <= 1, (a, b)
    if a >= -F(1, 2) and b <= F(1, 2):
        return _asin_series_iv(a, b)
    if b <= -F(1, 2):                      # oddness
        return -asin_iv(-b, -a)
    if a >= F(1, 2):                       # asin(x) = pi/2 - 2 asin(sqrt((1-x)/2))
        ta = sqrt_iv(Iv((1 - a) / 2))
        tb = sqrt_iv(Iv((1 - b) / 2))
        return HALF_PI - 2 * asin_iv(tb.lo, ta.hi)
    if a < -F(1, 2):
        return hull(asin_iv(a, -F(1, 2)), asin_iv(-F(1, 2), b))
    return hull(asin_iv(a, F(1, 2)), asin_iv(F(1, 2), b))


def acos_iv(a, b):
    return HALF_PI - asin_iv(a, b)
