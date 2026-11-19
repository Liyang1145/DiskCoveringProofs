# SPDX-License-Identifier: MIT
"""Exact upper certificate r_D(19) <= 1/sqrt(13), no optimality claim.

Scale the target disk to radius sqrt(13). Coordinates (X,Y) represent
physical coordinates (sqrt(3)*X,Y), so the metric is 3*X^2+Y^2.

The nearest-center squared distance is continuous, hence has a maximum.
On a closed Voronoi cell it is the strictly convex squared distance to
that cell's center. A maximum in the interior of the target disk must
have at least two independent active bisectors: otherwise the point
lies inside a nontrivial segment in the cell and strict convexity
contradicts maximality. Two independent bisectors give a triple
circumcenter. On the boundary, the pairwise bisector intersections
split the circle into arcs of fixed nearest center. On an open arc a
nonconstant squared distance to that center only has stationary points
parallel to the center vector, in the weighted coordinates. A constant
arc (origin is nearest) is covered by its endpoints, or a single fixed
boundary point if there are no intersections at all. We enumerate a
superset of all needed points and check each is covered at radius 1.
"""
from fractions import Fraction as F
from itertools import combinations, product


def _dot(p, q):
    return 3*p[0]*q[0] + p[1]*q[1]


def _norm(p):
    return _dot(p, p)


def _bisector(c, d):
    return 6*(d[0]-c[0]), 2*(d[1]-c[1]), _norm(d)-_norm(c)


def _nonpositive(a, b, s):
    """Decide exactly whether a + b*sqrt(s) <= 0, s >= 0."""
    if not b or not s:
        return a <= 0
    if b > 0:
        return a <= 0 and a*a >= b*b*s
    return a <= 0 or a*a <= b*b*s


def _covered(p, v, s, centers):
    # Distance squared at p + sqrt(s)*v minus 1.
    for c in centers:
        u = p[0]-c[0], p[1]-c[1]
        if _nonpositive(_norm(u)+s*_norm(v)-1, 2*_dot(u,v), s):
            return True
    return False


def check_n19_upper():
    """Check exactly; raise ArithmeticError on any uncovered critical point."""
    centers = [(F(2*a+b,2), F(3*b,2))
               for a,b in product(range(-2,3), repeat=2)
               if max(abs(a), abs(b), abs(a+b)) <= 2]
    origin = F(0), F(0)
    counts = {"interior_triples": 0, "boundary_bisectors": 0,
              "boundary_stationary": 0, "boundary_reference": 0}

    def check(kind, p, v=origin, s=F(0)):
        if not _covered(p, v, s, centers):
            raise ArithmeticError(f"uncovered {kind}: {p} + sqrt({s}) * {v}")
        counts[kind] += 1

    for c,d,e in combinations(centers, 3):
        a,b,f = _bisector(c,d)
        A,B,g = _bisector(c,e)
        det = a*B-b*A
        if det:
            p = (f*B-b*g)/det, (a*g-f*A)/det
            if _norm(p) < 13:
                check("interior_triples", p)

    for c,d in combinations(centers, 2):
        a,b,f = _bisector(c,d)
        # Metric-orthogonal projection of the origin onto a*X+b*Y=f.
        h = a*a/3+b*b
        p = f*a/(3*h), f*b/h
        v = -b, a
        s = (13-_norm(p))/_norm(v)
        if s >= 0:
            check("boundary_bisectors", p, v, s)
            if s:
                check("boundary_bisectors", p, (-v[0],-v[1]), s)

    for c in centers:
        if c != origin:
            s = 13/_norm(c)
            check("boundary_stationary", origin, c, s)
            check("boundary_stationary", origin, (-c[0],-c[1]), s)
    check("boundary_reference", origin, (F(0),F(1)), F(13))
    return {"n": 19, "status": "certified_upper_only",
            "upper_exact": "1/sqrt(13)", "upper_squared": "1/13",
            "weighted_centers": [[str(x),str(y)] for x,y in centers],
            "coordinates": "(sqrt(3)*X/sqrt(13), Y/sqrt(13))",
            "checked": counts}
