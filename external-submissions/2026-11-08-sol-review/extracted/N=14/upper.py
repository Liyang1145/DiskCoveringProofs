"""Prove the exact 14-disk construction using outward-rounded intervals."""

from collections import Counter
import argparse

from interval import Interval as I, SCALE


ROOT_R = I("0.33173203427623412255781554880",
           "0.33173203427623412255781554881")
ROOT_T = I("0.0568866625220515", "0.0568866625220517")


class Jet:
    """An interval enclosure for a value and its r, t, tt derivatives."""
    def __init__(self, value, dr=0, dt=0, dtt=0):
        self.v = I.coerce(value)
        self.r = I.coerce(dr)
        self.t = I.coerce(dt)
        self.tt = I.coerce(dtt)

    @classmethod
    def wrap(cls, value):
        return value if isinstance(value, cls) else cls(value)

    def __add__(self, other):
        other = self.wrap(other)
        return Jet(self.v + other.v, self.r + other.r,
                   self.t + other.t, self.tt + other.tt)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.r, -self.t, -self.tt)

    def __sub__(self, other):
        return self + (-self.wrap(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = self.wrap(other)
        return Jet(self.v * other.v,
                   self.r * other.v + self.v * other.r,
                   self.t * other.v + self.v * other.t,
                   self.tt * other.v + 2 * self.t * other.t + self.v * other.tt)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.wrap(other)
        v = other.v.reciprocal()
        first = -v.square()
        second = -2 * v * first
        return self * Jet(v, first * other.r, first * other.t,
                          first * other.tt + second * other.t.square())

    def square(self):
        return self * self

    def sqrt(self):
        root = self.v.sqrt()
        first = 1 / (2 * root)
        second = -first / (2 * self.v)
        return Jet(root, first * self.r, first * self.t,
                   first * self.tt + second * self.t.square())


def geometry(r, t):
    a = r + t
    b = (r.square() - t.square()).sqrt()
    e = (1 - r.square()).sqrt()
    d = (e + b) / 2
    delta = (e - b) / 2
    h = (r.square() - delta.square()).sqrt()
    c = r + h
    factor = 2 * (r*c + e*d) / (c.square() + d.square())
    sx, sy = factor*c - r, factor*d - e
    scale = (1 - ((r.square() - (1 - sx)/2) / ((1 + sx)/2)).sqrt()) / 2
    px, py = scale*(1+sx), scale*sy
    F = (px - a - h).square() + (py - delta).square() - r.square()
    coordinates = {
        "A": (a, 0), "B": (0, b), "E": (0, e), "P": (px, py), "Q": (c, d),
        "O": (0, 0), "X": (1, 0), "Y": (0, 1), "S": (sx, sy), "T": (r, e),
        "H": (t, 0), "L": (a+r, 0), "M": (0, e-r),
        "U": (a+h, delta), "V": (h, d), "W": (r, b),
    }
    return F, coordinates


def derivatives(r, t):
    return geometry(Jet(r, dr=1), Jet(t, dt=1))[0]


def approximate():
    r = I("0.331732034276234")
    t = I("0.05688666")
    for _ in range(10):
        j = derivatives(r, t)
        t = (t - j.t / j.tt).midpoint()
        j = derivatives(r, t)
        r = (r - j.v / j.r).midpoint()
    print("Numerical iteration for r:", r)
    print("Numerical iteration for t:", t)


def orient(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def distance2(a, b):
    return (a[0]-b[0]).square() + (a[1]-b[1]).square()


def geometry_checks(r, t):
    _, coords = geometry(r, t)
    coords = {k: tuple(map(I.coerce, p)) for k, p in coords.items()}
    r2 = r.square()
    for disk, vertex in [("P", "L"), ("E", "Y"), ("B", "M"), ("B", "O")]:
        assert (r2 - distance2(coords[disk], coords[vertex])).lo > 0, (disk, vertex)
    assert (coords["P"][0]).lo > 0
    assert coords["S"][0].lo > coords["T"][0].hi > 0
    assert coords["S"][1].lo > 0
    assert t.lo > 0
    assert (coords["L"][0]-t).lo > 0
    assert (1-coords["L"][0]).lo > 0
    assert coords["M"][1].lo > 0 and coords["M"][1].hi < I(1).lo
    # At X, the P disks with positive x-coordinate are the nearest disks.
    assert r.hi < SCALE
    assert (1 - coords["A"][0] - r).lo > 0
    assert (1 - coords["Q"][0] - r).lo > 0
    assert (coords["P"][0] - coords["Q"][0]).lo > 0
    assert coords["Q"][0].lo > 0 and coords["Q"][1].lo > 0
    assert coords["P"][1].lo > 0 and coords["A"][0].lo > 0
    assert coords["B"][1].lo > 0 and (coords["E"][1]-coords["B"][1]).lo > 0

    # Fan triangulations in the order given in the proof.
    faces = ["LXSU", "HLUW", "USTVW", "OHWVM", "MVTY"]
    outer = "OHLXSTYM"
    edges = Counter()
    for face in faces:
        for i in range(1, len(face)-1):
            triangle = face[0] + face[i:i+2]
            assert orient(*(coords[k] for k in triangle)).lo > 0, triangle
        for p, q in zip(face, face[1:]+face[0]):
            edges[p, q] += 1
            edges[q, p] -= 1
    for p, q in zip(outer, outer[1:]+outer[0]):
        edges[p, q] -= 1
        edges[q, p] += 1
    assert all(n == 0 for n in edges.values())

    print("All strict vertex distances, triangle orientations and edge cancellations certified.")
    for label in ["A", "B", "E", "P", "Q"]:
        print(label, *coords[label])


def certify():
    r, t = ROOT_R, ROOT_T
    j = derivatives(r, t)
    assert j.r.hi < 0
    assert j.tt.lo > 0
    assert derivatives(r, I.endpoints(t.lo, t.lo)).t.hi < 0
    assert derivatives(r, I.endpoints(t.hi, t.hi)).t.lo > 0
    lo = derivatives(I.endpoints(r.lo, r.lo), t.midpoint())
    hi = derivatives(I.endpoints(r.hi, r.hi), t.midpoint())
    assert (lo.v + lo.t * (t - t.midpoint())).lo > 0
    assert hi.v.hi < 0
    print("Unique root of F = F_t = 0 in")
    print("r =", r)
    print("t =", t)
    geometry_checks(r, t)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--approximate", action="store_true")
    args = parser.parse_args()
    if args.approximate:
        approximate()
        return
    certify()


if __name__ == "__main__":
    main()
