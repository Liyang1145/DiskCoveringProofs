"""Rational interval checks for the exact dihedrally symmetric solution."""
from fractions import Fraction as Q
from math import isqrt

SCALE = 10**36


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = Q(hi) if hi is not None else self.lo
        assert self.lo <= self.hi

    def __add__(self, value):
        other = interval(value)
        return Interval(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -interval(other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, value):
        other = interval(value)
        products = (
            self.lo*other.lo, self.lo*other.hi,
            self.hi*other.lo, self.hi*other.hi,
        )
        return Interval(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, value):
        other = interval(value)
        assert other.lo*other.hi > 0
        return self * Interval(1/other.hi, 1/other.lo)

    def sqrt(self):
        assert self.lo >= 0

        def scaled_root(value):
            return isqrt((value.numerator*SCALE*SCALE)//value.denominator)

        return Interval(Q(scaled_root(self.lo), SCALE),
                        Q(scaled_root(self.hi)+1, SCALE))


def interval(value):
    return value if isinstance(value, Interval) else Interval(value)


def parameters(r, u):
    b = u+r
    delta = (4*r*r - 3*u*u).sqrt()
    a = (u+delta)/2
    v = a+r
    x = (1+b)/2
    y = (r*r - (1-b)*(1-b)/4).sqrt()
    t = (b+r*r).sqrt()
    return a, b, v, x, y, t, delta


def cos_arc(r, t):
    return (1+t*t-r*r)/(2*t)


def alpha_prime(r, t):
    cosine = cos_arc(r, t)
    return ((1-r*r)/(t*t) - 1) / (2*(1-cosine*cosine).sqrt())


def slope(r, u):
    _, _, v, _, _, t, delta = parameters(r, u)
    return alpha_prime(r, t)/t + alpha_prime(r, v)*(1-3*u/delta)/2


def cosine_difference(r, u):
    _, _, v, x, y, _, _ = parameters(r, u)
    return (x*x-y*y+2*Interval(3).sqrt()*x*y)/(2*(x*x+y*y)) - cos_arc(r, v)


def verify_reduction_bounds():
    high_radius = Q(".36111")
    angle_limit = Q(".370")
    assert angle_limit-angle_limit**3/6 > high_radius
    assert Q("3.14159")-3*angle_limit > 6*Q(".330")
    assert Q("3.14159")/3-2*angle_limit > Q(".307")
    for t, phi in ((Q(".78111"), Q(".330")), (Q(".755"), Q(".307"))):
        assert (1+t*t-high_radius**2)/(2*t) > 1-phi**2/2+phi**4/24
    assert 3*Q(".42")**2/4 > high_radius**2
    a, u = Q(".39389"), Q(".32")
    assert a*a-a*u+u*u > high_radius**2
    assert 1-2*high_radius**2 > u+high_radius


def certify_symmetric_root():
    verify_reduction_bounds()
    r0 = Interval(".36110296374450864411")
    r1 = Interval(".36110296374450864412")
    test_u = Interval(".27824166087442791214863102289847881037")
    derivative = slope(r0, test_u)
    # For F<0, the 1-Lipschitz property of cosine gives F <= J.
    # The tangent bounds F from above on 0 <= u <= .32 by concavity.
    assert cosine_difference(r0, test_u).hi + Q(".32")*max(
        abs(derivative.lo), abs(derivative.hi)
    ) < 0
    assert cosine_difference(r1, test_u).lo > 0

    r = Interval(r0.lo, r1.hi)
    u = Interval(".27824166087", ".27824166088")
    assert slope(r, Interval(u.lo)).lo > 0
    assert slope(r, Interval(u.hi)).hi < 0

    # Check the common point M of the three perpendicular bisectors.
    _, _, v, x, y, _, _ = parameters(r, u)
    low_x = v/2
    low_y = Interval(3).sqrt()*low_x
    a11, a12 = 2*(x-u), 2*y
    a21, a22 = 2*(low_x-u), 2*low_y
    b1, b2 = x*x+y*y-u*u, v*v-u*u
    det = a11*a22-a12*a21
    mx = (b1*a22-b2*a12)/det
    my = (a11*b2-a21*b1)/det
    assert mx.lo > 0 and my.lo > 0
    assert (Interval(3).sqrt()*mx-my).lo > 0
    assert (mx*mx+my*my).hi < 1
    assert ((mx-u)*(mx-u)+my*my).hi < (r*r).lo
    print("Symmetric optimum: .36110296374450864411 < r < .36110296374450864412.")


if __name__ == "__main__":
    certify_symmetric_root()
