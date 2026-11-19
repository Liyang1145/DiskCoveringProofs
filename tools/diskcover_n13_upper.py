# SPDX-License-Identifier: MIT
"""Fixed rational n=13 upper witness, checked by exact Voronoi extrema.

All boundary points examined have coordinates p+sqrt(s)*v, for rational p,
v, and nonnegative rational s. The maximum of the nearest-center squared
distance is attained at one of the checked points: this follows by strict
convexity on straight cell faces and by elementary differentiation on
open boundary arcs of a nearest-center cell.
"""
from fractions import Fraction as F
from itertools import combinations
import json


CENTERS = (
    (741387397581048215, -230830229126290826),
    (823343225836765713, 298254014140025930),
    (440474695474615814, 753994783480230162),
    (-34698722166580616, 711948557539035266),
    (-460523278988366702, 668160709043508388),
    (-813137159102941013, 253169446040272273),
    (-758423147300240871, -288642951133260903),
    (-432717212335111085, -566419071051493595),
    (-65395828411870431, -870775215825060044),
    (508513268554909325, -712926209495437783),
    (242308637425765493, 175375059912787558),
    (-232539267581476872, 72400869763670615),
    (99927208321364971, -281929850224561065),
)
SCALE = 10**18
UPPER = F("0.346645456927389645")


def _dot(a, b):
    return a[0]*b[0] + a[1]*b[1]


def _norm(a):
    return _dot(a, a)


def _bisect(a, b):
    return 2*(b[0]-a[0]), 2*(b[1]-a[1]), _norm(b)-_norm(a)


def _nonpositive(a, b, s):
    """Sign of a + b*sqrt(s) without approximating its radical."""
    if not b or not s:
        return a <= 0
    if b > 0:
        return a <= 0 and a*a >= b*b*s
    return a <= 0 or a*a <= b*b*s


def _check_fixed(centers, bound):
    origin = F(0), F(0)
    counts = dict(interior_triples=0, boundary_pairs=0, stationary=0, reference=0)

    def check(kind, p, v=origin, s=F(0)):
        for x, y in centers:
            w = p[0]-x, p[1]-y
            if _nonpositive(_norm(w)+s*_norm(v)-bound**2, 2*_dot(w,v), s):
                counts[kind] += 1
                return
        raise ArithmeticError(f"not covered at {bound}: {kind} {p}+sqrt({s})*{v}")

    for x,y,z in combinations(centers, 3):
        a,b,f = _bisect(x,y)
        A,B,g = _bisect(x,z)
        det = a*B-b*A
        if det:
            p = ((f*B-b*g)/det, (a*g-f*A)/det)
            if _norm(p) < 1:
                check("interior_triples", p)

    for x,y in combinations(centers, 2):
        a,b,f = _bisect(x,y)
        h = a*a+b*b
        p = (f*a/h, f*b/h)
        s = (1-_norm(p))/h
        if s >= 0:
            check("boundary_pairs", p, (-b,a), s)
            if s:
                check("boundary_pairs", p, (b,-a), s)

    for c in centers:
        if c != origin:
            s = 1/_norm(c)
            check("stationary", origin, c, s)
            check("stationary", origin, (-c[0],-c[1]), s)
    check("reference", (F(1),F(0)))
    return counts


def check_n13_upper():
    """Check the independent exact rational geometry; no proof of optimality."""
    if len(CENTERS) != 13 or len(set(CENTERS)) != 13:
        raise ArithmeticError("expected thirteen distinct rational centers")
    centers = [(F(x,SCALE), F(y,SCALE)) for x,y in CENTERS]
    return {
        "n": 13, "status": "certified_upper_only",
        "upper_exact": "0.346645456927389645", "upper_rational": str(UPPER),
        "upper_squared": str(UPPER**2),
        "center_numerators": [list(p) for p in CENTERS],
        "center_denominator": SCALE,
        "source": (
            "https://github.com/VonEquinox/DiskCoveringSolve/blob/"
            "089584973f41e6374ce110f6e5b5ee456df19352/cover13/docs/cover13_proof_zh.md"
        ),
        "checked": _check_fixed(centers, UPPER),
    }


if __name__ == "__main__":
    print(json.dumps(check_n13_upper(), indent=2))
