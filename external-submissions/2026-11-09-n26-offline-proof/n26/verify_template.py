"""Prove existence and local template optimality of an exact algebraic cover."""

import json
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from pathlib import Path

from refine_template import dot, solve_linear, sub, template


SCALE = 10**90
N = 3


def ceil_div(a, b):
    return -((-a) // b)


def require(test, why):
    if not test:
        raise ValueError(why)


class Interval:
    """Closed interval with outward-rounded decimal rational endpoints."""

    def __init__(self, lo, hi=None):
        lo = Q(lo) * SCALE
        hi = lo if hi is None else Q(hi) * SCALE
        self.lo = lo.numerator // lo.denominator
        self.hi = ceil_div(hi.numerator, hi.denominator)

    @classmethod
    def raw(cls, lo, hi):
        x = object.__new__(cls)
        x.lo, x.hi = lo, hi
        return x

    @staticmethod
    def cast(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, y):
        y = self.cast(y)
        return self.raw(self.lo + y.lo, self.hi + y.hi)

    __radd__ = __add__

    def __neg__(self):
        return self.raw(-self.hi, -self.lo)

    def __sub__(self, y):
        return self + (-self.cast(y))

    def __rsub__(self, y):
        return self.cast(y) + (-self)

    def __mul__(self, y):
        y = self.cast(y)
        prod = [a * b for a in (self.lo, self.hi) for b in (y.lo, y.hi)]
        return self.raw(min(prod) // SCALE, ceil_div(max(prod), SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        require(self.lo * self.hi > 0, "Division interval contains zero")
        return self.raw(SCALE**2 // self.hi, ceil_div(SCALE**2, self.lo))

    def __truediv__(self, y):
        return self * self.cast(y).reciprocal()

    def __rtruediv__(self, y):
        return self.cast(y) * self.reciprocal()

    def __pow__(self, power):
        require(power == 2, "Only the square is used")
        hi = max(self.lo * self.lo, self.hi * self.hi)
        lo = min(self.lo * self.lo, self.hi * self.hi) if self.lo * self.hi > 0 else 0
        return self.raw(lo // SCALE, ceil_div(hi, SCALE))

    def sqrt(self):
        require(self.lo >= 0, "Negative square-root interval")
        lo = isqrt(self.lo * SCALE)
        hi = isqrt(self.hi * SCALE)
        return self.raw(lo, hi + (hi * hi < self.hi * SCALE))

    def magnitude(self):
        return Q(max(abs(self.lo), abs(self.hi)), SCALE)

    def midpoint(self):
        return Q(self.lo + self.hi, 2 * SCALE)


class Jet:
    """Value, first derivative and second derivative intervals in r,d,k."""

    def __init__(self, value, gradient=None, hessian=None, n=N):
        self.v = Interval.cast(value)
        self.g = (Interval(0),) * n if gradient is None else gradient
        self.n = len(self.g)
        self.h = ((Interval(0),) * self.n,) * self.n if hessian is None else hessian

    @classmethod
    def variable(cls, x, k, n=N):
        return cls(x, tuple(Interval(i == k) for i in range(n)))

    def cast(self, x):
        return x if isinstance(x, Jet) else Jet(x, n=self.n)

    def __add__(self, y):
        y = self.cast(y)
        return Jet(self.v + y.v, tuple(a + b for a, b in zip(self.g, y.g)),
                   tuple(tuple(a + b for a, b in zip(row, other))
                         for row, other in zip(self.h, y.h)))

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, tuple(-a for a in self.g), tuple(tuple(-a for a in row) for row in self.h))

    def __sub__(self, y):
        return self + (-self.cast(y))

    def __rsub__(self, y):
        return self.cast(y) + (-self)

    def __mul__(self, y):
        y = self.cast(y)
        g = tuple(self.g[i] * y.v + self.v * y.g[i] for i in range(self.n))
        h = tuple(tuple(
            self.h[i][j] * y.v + self.v * y.h[i][j] + self.g[i] * y.g[j] + self.g[j] * y.g[i]
            for j in range(self.n)) for i in range(self.n))
        return Jet(self.v * y.v, g, h)

    __rmul__ = __mul__

    def compose(self, value, first, second):
        return Jet(value, tuple(first * a for a in self.g),
                   tuple(tuple(first * self.h[i][j] + second * self.g[i] * self.g[j]
                               for j in range(self.n)) for i in range(self.n)))

    def reciprocal(self):
        v = self.v.reciprocal()
        return self.compose(v, -(v**2), 2 * v * v * v)

    def __truediv__(self, y):
        return self * self.cast(y).reciprocal()

    def __rtruediv__(self, y):
        return self.cast(y) * self.reciprocal()

    def __pow__(self, power):
        require(power == 2, "Only the square is used")
        return self.compose(self.v**2, 2 * self.v, Interval(2))

    def sqrt(self):
        v = self.v.sqrt()
        return self.compose(v, 1 / (2 * v), -1 / (4 * v * v * v))


def system(box):
    f = template(*(Jet.variable(x, i) for i, x in enumerate(box)))[0]
    return (f.v, f.g[1], f.g[2]), (f.g, f.h[1], f.h[2])


def inverse_midpoint(matrix):
    mid = [[x.midpoint() for x in row] for row in matrix]
    columns = [solve_linear(mid, [Q(i == j) for i in range(N)]) for j in range(N)]
    return tuple(zip(*columns))


def cross(p, q):
    return p[0] * q[1] - p[1] * q[0]


def root_box():
    center = list(map(Q, [
        "0.23470009040044823961679013377669212756049596365497139178592406224",
        "0.20556460035923095267235988860729022087093734912660428302269045106",
        "0.13840802072094331297267465884175501359649327478692298589095147330",
    ]))
    eps = Q("1e-60")
    box = [Interval(x - eps, x + eps) for x in center]
    return center, eps, box


@lru_cache(maxsize=1)
def certified_trial_radius():
    path = Path(__file__).with_name("upper_refined.json")
    radius = Q(json.loads(path.read_text(encoding="utf-8"))["radius"])
    center,width,_ = root_box()
    require(center[0]+width < radius, "The rational radius may be below the algebraic radius")
    return radius


def main():
    center, eps, box = root_box()
    mid = [Interval(x) for x in center]
    gmid, jmid = system(mid)
    _, jbox = system(box)
    inverse = inverse_midpoint(jmid)

    def prod(row, col):
        return sum(Interval(a) * b for a, b in zip(row, col))

    lipschitz = max(sum((Q(i == j) - prod(row, col)).magnitude()
                        for j, col in enumerate(zip(*jbox)))
                    for i, row in enumerate(inverse))
    movement = max(prod(row, gmid).magnitude() for row in inverse)
    require(lipschitz < 1 and movement + lipschitz * eps < eps, "Contraction test failed")

    # At the zero, the implicit graph r(d,k) has positive definite Hessian.
    require(jbox[0][0].hi < 0, "F_r is not strictly negative")
    hdd, hdk, hkk = jbox[1][1], jbox[1][2], jbox[2][2]
    require(hdd.lo > 0 and (hdd * hkk - hdk**2).lo > 0, "Hessian is not positive definite")

    r = box[0]
    _, outer, middle, _, seams = template(*box, with_seams=True)
    require(all(p[0].lo > 0 and p[1].lo > 0 for p in seams), "Seam not in first quadrant")
    require(all(cross(a, b).lo > 0 for a, b in zip(seams, seams[1:])), "Seams out of order")
    require(all(p[0].lo >= 0 and p[1].lo >= 0 for p in outer), "Outer center out of quadrant")

    p, q, s = outer[2], outer[3], middle[1]
    a, b, c = sub(q, p), sub(s, p), sub(s, q)
    # Only the slack triangle needs an inequality. The other circumcenters
    # and the seam equalities are explicit identities in proof.md.
    radius2 = dot(a, a) * dot(b, b) * dot(c, c) / (4 * cross(a, b)**2)
    require((r**2 - radius2).lo > 0, "Slack triangle is not covered")
    print("PASS: algebraic template zero exists and is unique in the stated box")
    print(f"contraction <= {float(lipschitz):.6g}, center movement <= {float(movement):.6g}")
    print("PASS: seam order, slack triangle, and strict local minimum in the template")


if __name__ == "__main__":
    main()
