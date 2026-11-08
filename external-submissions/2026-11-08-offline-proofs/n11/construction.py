"""Certify the exact radius and coordinates of a symmetric covering."""

from fractions import Fraction
from intervals import Interval as I

DIM = 4
ZERO = I(0)
CENTER = tuple(map(Fraction, (
    ".379983853119838689722261606136093214",
    ".272977466346363395009533747397017934",
    ".149428498926956476438885135016366164",
    ".033062070660392857534218746715927912",
)))
ETA = Fraction(1, 10**34)


class Jet:
    """A value and all first and second partial derivatives."""

    def __init__(self, value, gradient=None, hessian=None):
        self.v = I.get(value)
        self.g = gradient if gradient is not None else [ZERO] * DIM
        self.h = hessian if hessian is not None else [[ZERO] * DIM for _ in range(DIM)]

    @staticmethod
    def get(x):
        return x if isinstance(x, Jet) else Jet(x)

    def __neg__(self):
        return Jet(-self.v, [-a for a in self.g], [[-a for a in row] for row in self.h])

    def __add__(self, other):
        other = self.get(other)
        return Jet(self.v + other.v,
                   [a + b for a, b in zip(self.g, other.g)],
                   [[a + b for a, b in zip(row, column)] for row, column in zip(self.h, other.h)])

    __radd__ = __add__

    def __sub__(self, other):
        return self + -self.get(other)

    def __rsub__(self, other):
        return self.get(other) + -self

    def __mul__(self, other):
        other = self.get(other)
        gradient = [a * other.v + b * self.v for a, b in zip(self.g, other.g)]
        hessian = [[self.h[i][j] * other.v + other.h[i][j] * self.v
                    + self.g[i] * other.g[j] + self.g[j] * other.g[i]
                    for j in range(DIM)] for i in range(DIM)]
        return Jet(self.v * other.v, gradient, hessian)

    __rmul__ = __mul__

    def compose(self, value, first, second):
        gradient = [first * g for g in self.g]
        hessian = [[first * self.h[i][j] + second * self.g[i] * self.g[j]
                    for j in range(DIM)] for i in range(DIM)]
        return Jet(value, gradient, hessian)

    def inverse(self):
        v = 1 / self.v
        return self.compose(v, -v.square(), 2 * v.square() * v)

    def __truediv__(self, other):
        return self * self.get(other).inverse()

    def __rtruediv__(self, other):
        return self.inverse() * other

    def sqrt(self):
        v = self.v.sqrt()
        return self.compose(v, 1 / (2 * v), -1 / (4 * v * self.v))


def plus(a, b):
    return a[0] + b[0], a[1] + b[1]


def minus(a, b):
    return a[0] - b[0], a[1] - b[1]


def scale(k, a):
    return a[0] * k, a[1] * k


def j(a):
    return -a[1], a[0]


def norm2(a):
    return a[0] * a[0] + a[1] * a[1]


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def boundary(c, r, sign):
    u = norm2(c)
    k = (1 + u - r * r) / (2 * u)
    return plus(scale(k, c), scale(sign * (1 / u - k * k).sqrt(), j(c)))


def equal(a, b, r, sign):
    d = minus(b, a)
    h = (r * r / norm2(d) - Fraction(1, 4)).sqrt()
    return plus(scale(Fraction(1, 2), plus(a, b)), scale(h * sign, j(d)))


def geometry(r, a, b, t):
    p, q = (a, a * 0), (-b, b * 0)
    x = ((a - b) / 2, (r * r - (a + b) * (a + b) / 4).sqrt())
    c = plus(x, (t, (r * r - t * t).sqrt()))

    u = boundary(c, r, -1)
    v = minus(plus(c, p), x)
    right = equal(u, v, r, 1)
    u1 = boundary(right, r, -1)
    v1 = minus(plus(right, p), v)
    e = equal(u1, v1, r, 1)

    w = boundary(c, r, 1)
    z = minus(plus(c, q), x)
    left = equal(w, z, r, -1)
    w1 = boundary(left, r, 1)
    d = ((-1 - b - r) / 2, (r * r - (1 - b - r) * (1 - b - r) / 4).sqrt())
    return p, q, x, c, right, e, left, d, u, u1, v, v1, w, w1, z


def contact_jets(box):
    r, a, b, t = [Jet(x, [I(int(i == j)) for j in range(DIM)]) for i, x in enumerate(box)]
    p, q, x, c, right, e, left, d, u, u1, v, v1, w, w1, z = geometry(r, a, b, t)
    f = e[1]
    g = norm2(minus(w1, d)) - r * r
    return f, g


def equations(box):
    f, g = contact_jets(box)

    def minor(i):
        value = f.g[i] * g.g[3] - f.g[3] * g.g[i]
        gradient = [f.h[i][j] * g.g[3] + f.g[i] * g.h[3][j]
                    - f.h[3][j] * g.g[i] - f.g[3] * g.h[i][j] for j in range(DIM)]
        return value, gradient

    m1, dm1 = minor(1)
    m2, dm2 = minor(2)
    return [f.v, g.v, m1, m2], [f.g, g.g, dm1, dm2]


def inverse_mid(matrix):
    # All pivots and operations here are exact rationals.
    dimension = len(matrix)
    a = [[v.mid() for v in row] + [Fraction(i == j) for j in range(dimension)]
         for i, row in enumerate(matrix)]
    for j in range(dimension):
        pivot = max(range(j, dimension), key=lambda i: abs(a[i][j]))
        a[j], a[pivot] = a[pivot], a[j]
        a[j] = [v / a[j][j] for v in a[j]]
        for i in range(dimension):
            if i != j:
                a[i] = [v - a[i][j] * w for v, w in zip(a[i], a[j])]
    # Select an exact dyadic matrix near the inverse, rather than an interval matrix.
    return [[I(I(v).mid()) for v in row[dimension:]] for row in a]


def verify_root(center, eta):
    point = list(map(I, center))
    box = [I(v - eta, v + eta) for v in center]
    fx, jac = equations(point)
    a = inverse_mid(jac)
    _, whole_jac = equations(box)
    contraction = []
    residual = []
    for i in range(DIM):
        errors = [I(int(i == j)) - sum(a[i][k] * whole_jac[k][j] for k in range(DIM))
                  for j in range(DIM)]
        contraction.append(sum(z.abs_upper() for z in errors))
        residual.append(sum(a[i][k] * fx[k] for k in range(DIM)).abs_upper())
    assert 10 * max(contraction) < I.SCALE
    assert 10 * max(residual) < eta * I.SCALE
    return box


def verify_geometry(box):
    r, a, b, t = box
    p, q, x, c, right, e, left, d, u, u1, v, v1, w, w1, z = geometry(r, a, b, t)
    # The upper boundary seams occur from right to left in this order.
    seams = (u1, u, w, w1)
    for i, pt in enumerate(seams):
        assert pt[1].lo > 0
        if i:
            assert pt[0].hi < seams[i - 1][0].lo
    assert e[0].lo > 0 and d[1].lo > 0
    # Select the short arcs contained in each outer disk.
    for pt, start, end in (
        (right, u1, u), (c, u, w), (left, w, w1), (d, w1, (I(-1), ZERO))
    ):
        assert cross(start, pt).lo > 0 and cross(pt, end).lo > 0
        assert cross(start, end).lo > 0

    # A strict common point for the two non-tight triangles, one by reflection.
    witness = (I("-.386"), I(".296"))
    for pt in (left, d, q):
        assert (norm2(minus(pt, witness)) - r.square()).hi < 0

    # The leftmost boundary seam is at distance r from D and its reflection.
    # Every other site is strictly farther away, including the reflected sites.
    seam = (I(-1), ZERO)
    for pt in (e, right, c, left, p, q):
        assert (norm2(minus(pt, seam)) - r.square()).lo > 0

    return (e, right, c, left, d, p, q)


def verify_local_minimum(box):
    f, g = contact_jets(box)
    det = f.g[0]*g.g[3] - f.g[3]*g.g[0]
    assert (det.lo > 0 or det.hi < 0) and (f.g[3].lo > 0 or f.g[3].hi < 0)
    # At the root the first partial derivatives of r(a,b) vanish.
    directions = [[ZERO, I(i == 1), I(i == 2), -f.g[i]/f.g[3]] for i in (1, 2)]

    def second(i, j):
        quad_f = sum(directions[i][k]*f.h[k][l]*directions[j][l]
                     for k in range(DIM) for l in range(DIM))
        quad_g = sum(directions[i][k]*g.h[k][l]*directions[j][l]
                     for k in range(DIM) for l in range(DIM))
        return (f.g[3]*quad_g-g.g[3]*quad_f)/det

    rr, rs, ss = second(0, 0), second(0, 1), second(1, 1)
    assert rr.lo > 0 and (rr*ss-rs.square()).lo > 0


if __name__ == "__main__":
    box = verify_root(CENTER, ETA)
    pts = verify_geometry(box)
    verify_local_minimum(box)
    print("Certified a unique root in the specified box.")
    print("All geometric checks passed.")
    print("Strict local minimum within the symmetric contact family.")
    for label, point in zip(("E", "A", "C", "L", "D", "P", "Q"), pts):
        print(label, point)
