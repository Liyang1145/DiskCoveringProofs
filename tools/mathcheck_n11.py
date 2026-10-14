#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Portable, fail-closed arithmetic checks for the delivered eleven-disk candidate.

Only Python's standard library is used. Saved PASS flags, decimal residuals and
saved interval bounds are never accepted as mathematical evidence. This is a
scoped arithmetic checker, not a replay of the full global lower-bound proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as F
import hashlib
import json
from math import factorial, lcm
from pathlib import Path
import time

PRECISION = 64
DOWN = Context(prec=PRECISION, rounding=ROUND_FLOOR)
UP = Context(prec=PRECISION, rounding=ROUND_CEILING)
NEAR = Context(prec=PRECISION, rounding=ROUND_HALF_EVEN)
DEFAULT_DATA = Path(__file__).resolve().parents[1] / "math_data" / "n11"


def require(condition, message):
    # Assertions would disappear under python -O.
    if not condition:
        raise ValueError(message)


class Interval:
    """Closed Decimal intervals; every arithmetic endpoint is rounded outwards."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo=0, hi=None):
        if isinstance(lo, Interval) and hi is None:
            self.lo, self.hi = lo.lo, lo.hi
            return
        if isinstance(lo, F) and hi is None:
            self.lo = DOWN.divide(D(lo.numerator), D(lo.denominator))
            self.hi = UP.divide(D(lo.numerator), D(lo.denominator))
        else:
            self.lo = D(lo)
            self.hi = self.lo if hi is None else D(hi)
        require(self.lo.is_finite() and self.hi.is_finite() and self.lo <= self.hi,
                "invalid/nonfinite interval")

    def __add__(self, other):
        other = I(other)
        return I(DOWN.add(self.lo, other.lo), UP.add(self.hi, other.hi))

    __radd__ = __add__

    def __neg__(self):
        # Decimal unary minus otherwise depends on the ambient context.
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-I(other))

    def __rsub__(self, other):
        return I(other) - self

    def __mul__(self, other):
        other = I(other)
        products = [(a, b) for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(DOWN.multiply(a, b) for a, b in products),
                 max(UP.multiply(a, b) for a, b in products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = I(other)
        require(other.hi < 0 or other.lo > 0, "division interval contains zero")
        return self * I(DOWN.divide(D(1), other.hi), UP.divide(D(1), other.lo))

    def __rtruediv__(self, other):
        return I(other) / self

    def square(self):
        if self.lo >= 0:
            return I(DOWN.multiply(self.lo, self.lo), UP.multiply(self.hi, self.hi))
        if self.hi <= 0:
            return (-self).square()
        return I(0, max(UP.multiply(self.lo, self.lo), UP.multiply(self.hi, self.hi)))

    def sqrt(self):
        require(self.lo > 0, "strictly positive square-root branch required")
        # Decimal.sqrt is correctly rounded to nearest regardless of rounding
        # mode. One next_minus/next_plus encloses the exact square root.
        return I(DOWN.next_minus(NEAR.sqrt(self.lo)), UP.next_plus(NEAR.sqrt(self.hi)))

    def abs_upper(self):
        return max(self.lo.copy_abs(), self.hi.copy_abs())

    def midpoint(self):
        return NEAR.divide(NEAR.add(self.lo, self.hi), D(2))

    def record(self):
        return [str(self.lo), str(self.hi)]


I = Interval


def pi_interval():
    # Machin: pi = 16 atan(1/5) - 4 atan(1/239). Alternating rational
    # partial sums bracket each atan, independently of any saved decimal pi.
    def atan(q, terms):
        s = sum((F((-1) ** k, (2 * k + 1) * q ** (2 * k + 1))
                 for k in range(terms)), F(0))
        nxt = F((-1) ** terms, (2 * terms + 1) * q ** (2 * terms + 1))
        return I(min(I(s).lo, I(s + nxt).lo), max(I(s).hi, I(s + nxt).hi))
    return 16 * atan(5, 64) - 4 * atan(239, 20)


PI = pi_interval()


def trig(x, sine):
    """Taylor on all |x|<=8 with the Lagrange remainder, no monotonicity guess."""
    x = I(x)
    require(x.abs_upper() <= D(8), "trigonometric argument outside supported domain")
    xx = x.square()
    term = x if sine else I(1)
    out = term
    for k in range(1, 57):
        a = 2 * k + (1 if sine else 0)
        term = -term * xx / ((a - 1) * a)
        out += term
    degree = 113 if sine else 112
    # All real derivatives of sin/cos have magnitude <=1.
    remainder = I(x.abs_upper())
    for _ in range(degree):
        remainder *= x.abs_upper()
    remainder /= factorial(degree + 1)
    return out + I(remainder.hi.copy_negate(), remainder.hi)


def sin(x):
    return x.unary(trig(x.v, True), trig(x.v, False), -trig(x.v, True)) if isinstance(x, Jet) else trig(x, True)


def cos(x):
    return x.unary(trig(x.v, False), -trig(x.v, True), -trig(x.v, False)) if isinstance(x, Jet) else trig(x, False)


def sqrt(x):
    if not isinstance(x, Jet):
        return I(x).sqrt()
    root = x.v.sqrt()
    return x.unary(root, 1 / (2 * root), -1 / (4 * x.v * root))


class Jet:
    """Value, gradient and full Hessian with interval chain/product rules."""
    __slots__ = ("v", "g", "h")
    N = 7

    def __init__(self, v, g=None, h=None):
        self.v = I(v)
        self.g = [I(0) for _ in range(7)] if g is None else g
        self.h = [[I(0) for _ in range(7)] for _ in range(7)] if h is None else h

    @classmethod
    def variable(cls, v, k):
        out = cls(v)
        out.g[k] = I(1)
        return out

    def __add__(self, other):
        other = as_jet(other)
        return Jet(self.v + other.v, [a + b for a, b in zip(self.g, other.g)],
                   [[self.h[i][j] + other.h[i][j] for j in range(7)] for i in range(7)])

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, [-a for a in self.g], [[-a for a in row] for row in self.h])

    def __sub__(self, other):
        return self + (-as_jet(other))

    def __rsub__(self, other):
        return as_jet(other) - self

    def __mul__(self, other):
        other = as_jet(other)
        return Jet(self.v * other.v,
                   [self.g[i] * other.v + self.v * other.g[i] for i in range(7)],
                   [[self.h[i][j] * other.v + self.g[i] * other.g[j]
                     + self.g[j] * other.g[i] + self.v * other.h[i][j]
                     for j in range(7)] for i in range(7)])

    __rmul__ = __mul__

    def unary(self, value, first, second):
        return Jet(value, [first * a for a in self.g],
                   [[second * self.g[i] * self.g[j] + first * self.h[i][j]
                     for j in range(7)] for i in range(7)])

    def __truediv__(self, other):
        other = as_jet(other)
        reciprocal = 1 / other.v
        return self * other.unary(reciprocal, -reciprocal.square(),
                                 2 * reciprocal.square() * reciprocal)

    def __rtruediv__(self, other):
        return as_jet(other) / self


def as_jet(x):
    return x if isinstance(x, Jet) else Jet(x)


def squared_distance(p, q):
    a, b = p[0] - q[0], p[1] - q[1]
    return a * a + b * b


def model(z):
    a0, a1, a2, a3, y0, y1, radius = z
    a4 = PI - 2 * (a0 + a1 + a2 + a3) if not isinstance(a0, Jet) else as_jet(PI) - 2 * (a0 + a1 + a2 + a3)
    angles = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    zero = Jet(0) if isinstance(a0, Jet) else I(0)
    theta = [zero for _ in range(9)]
    for k in range(5, 9):
        theta[k] = theta[k - 1] + angles[k - 1] + angles[k]
    for k in range(3, -1, -1):
        theta[k] = theta[k + 1] - angles[k] - angles[k + 1]
    rho = [cos(a) - sqrt(radius * radius - sin(a) * sin(a)) for a in angles]
    sites = [(rho[k] * cos(theta[k]), rho[k] * sin(theta[k])) for k in range(9)]
    sites += [(y0, zero), (y1, zero)]
    boundary = [(cos(theta[k] + angles[k]), sin(theta[k] + angles[k])) for k in range(9)]
    pins = [tuple(sites[k][j] + sites[(k + 1) % 9][j] - boundary[k][j]
                  for j in range(2)) for k in range(9)]
    m, d = (y0 + y1) / 2, (y1 - y0) / 2
    waist = (m, sqrt(radius * radius - d * d))
    return angles, theta, rho, sites, boundary, pins, waist


def system(u):
    z = [Jet.variable(u[k], k) for k in range(7)]
    _, _, _, sites, _, pins, waist = model(z)
    constraints = [sqrt(squared_distance(pins[k], sites[hub])) - z[6]
                   for k, hub in ((1, 10), (2, 9), (3, 9), (8, 10))]
    constraints += [sqrt(squared_distance(waist, sites[6])) - z[6]]
    multipliers = u[7:]
    residual = [f.v for f in constraints]
    residual += [I(int(i == 6)) - sum(multipliers[k] * constraints[k].g[i] for k in range(5))
                 for i in range(7)]
    jac = [[I(0) for _ in range(12)] for _ in range(12)]
    for k, f in enumerate(constraints):
        for i in range(7):
            jac[k][i] = f.g[i]
            jac[5 + i][7 + k] = -f.g[i]
    for i in range(7):
        for j in range(7):
            jac[5 + i][j] = -sum(multipliers[k] * constraints[k].h[i][j] for k in range(5))
    return residual, jac


def inverse_proposal(matrix):
    """Approximate inverse proposes fixed exact decimals; no accuracy premise."""
    n = len(matrix)
    rows = [[x.midpoint() for x in row] + [D(int(i == j)) for j in range(n)]
            for i, row in enumerate(matrix)]
    for i in range(n):
        p = max(range(i, n), key=lambda k: rows[k][i].copy_abs())
        require(rows[p][i] != 0, "singular inverse proposal")
        rows[i], rows[p] = rows[p], rows[i]
        pivot = rows[i][i]
        rows[i] = [NEAR.divide(v, pivot) for v in rows[i]]
        for k in range(n):
            if k != i:
                factor = rows[k][i]
                rows[k] = [NEAR.subtract(v, NEAR.multiply(factor, w))
                           for v, w in zip(rows[k], rows[i])]
    return [[I(v) for v in row[n:]] for row in rows]


def krawczyk(center, box, preconditioner, residual):
    # A fixed centre can lie outside later contracted boxes. The MVT needs
    # hull(centre, box); using only box is mathematically incorrect.
    hull = [I(min(c.lo, x.lo), max(c.hi, x.hi)) for c, x in zip(center, box)]
    _, jac = system(hull)
    e = [[I(int(i == j)) - sum(preconditioner[i][k] * jac[k][j] for k in range(12))
          for j in range(12)] for i in range(12)]
    q = max(UP.add(D(0), sum_outward(row)) for row in e)
    shifts = [-sum(preconditioner[i][k] * residual[k] for k in range(12))
              + sum(e[i][j] * (box[j] - center[j]) for j in range(12)) for i in range(12)]
    return [center[i] + shifts[i] for i in range(12)], q


def sum_outward(row):
    out = D(0)
    for v in row:
        out = UP.add(out, v.abs_upper())
    return out


def root_check(data):
    require(data.get("schema") == "n11-exact-tc-root-input-v1", "wrong root schema")
    require(len(data["center_hex"]) == 12, "root must have twelve coordinates")
    # float.fromhex parses an exact binary64 dyadic; Fraction.from_float
    # recovers its exact rational value without any decimal conversion.
    exact_center = [F.from_float(float.fromhex(x)) for x in data["center_hex"]]
    exact_rad = F.from_float(float.fromhex(data["radius_hex"]))
    center = [I(x) for x in exact_center]
    rad = I(exact_rad)
    require(rad.lo > 0, "root radius must be positive")
    box = [c + I(rad.hi.copy_negate(), rad.hi) for c in center]
    residual, jac = system(center)
    y = inverse_proposal(jac)
    image, q = krawczyk(center, box, y, residual)
    require(q < 1, "Krawczyk contraction failed")
    require(all(c - exact_rad < F(k.lo) and F(k.hi) < c + exact_rad
                for c, k in zip(exact_center, image)),
            "Krawczyk strict inclusion failed")
    initial_q = q
    for _ in range(6):
        box = [I(max(x.lo, k.lo), min(x.hi, k.hi)) for x, k in zip(box, image)]
        # Recentring uses exact finite decimal points. This avoids the
        # precision floor caused by retaining the original binary64 centre.
        center = [I(x.midpoint()) for x in box]
        residual, _ = system(center)
        image, q = krawczyk(center, box, y, residual)
    box = [I(max(x.lo, k.lo), min(x.hi, k.hi)) for x, k in zip(box, image)]
    threshold = I(F(3799838531198387090485182, 10 ** 25))
    require(box[6].hi < threshold.lo, "same-root energy threshold comparison failed")
    require(box[6].hi < I(F(19, 50)).lo, "same-root 19/50 comparison failed")
    require(box[6].lo > D("0.3799838531198386897222616061358") and
            box[6].hi < D("0.3799838531198386897222616061364"),
            "published radius decimal enclosure failed")
    # A deliberately shifted multiplier box must fail inclusion.
    bad_center = [I(F.from_float(float.fromhex(x))) for x in data["center_hex"]]
    bad_center[7] += I(F(1, 100))
    bad_box = [c + I(rad.hi.copy_negate(), rad.hi) for c in bad_center]
    bad_residual, bad_jac = system(bad_center)
    bad_image, _ = krawczyk(bad_center, bad_box, inverse_proposal(bad_jac), bad_residual)
    require(not all(x.lo < k.lo and k.hi < x.hi for x, k in zip(bad_box, bad_image)),
            "negative root control unexpectedly passed")
    return box, {"status": "PASS", "system_dimension": 12,
                 "contraction_upper": str(initial_q), "radius_enclosure": box[6].record(),
                 "same_root_below_energy_threshold": True, "negative_control_rejected": True}


FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9),
         (6, 7, 10), (8, 0, 10), (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]


def orient(p, q, r):
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])


def circumcenter(sites, face):
    p, q, r = [sites[k] for k in face]
    a, b = [2 * (q[k] - p[k]) for k in range(2)]
    c, d = [2 * (r[k] - p[k]) for k in range(2)]
    e = squared_distance(q, (0, 0)) - squared_distance(p, (0, 0))
    f = squared_distance(r, (0, 0)) - squared_distance(p, (0, 0))
    det = a * d - b * c
    return ((e * d - b * f) / det, (a * f - e * c) / det)


def geometry_check(box):
    angles, theta, rho, sites, boundary, pins, waist = model(box[:7])
    r = box[6]
    require(all(a.lo > 0 and a.hi < (PI / 2).lo for a in angles), "invalid boundary halfwidths")
    require(all((r.square() - sin(a).square()).lo > 0 for a in angles), "illegal ring sqrt branch")
    require(all(x.lo > 0 and x.hi < 1 for x in rho), "illegal ring radial branch")
    require(all(((1 - r).square() - squared_distance(sites[k], (0, 0))).lo > 0
                for k in (9, 10)), "hub not strictly interior")
    # Nine boundary arcs tile by the construction sum(a)=pi. Check every
    # other site is strictly farther away at each two-site boundary switch.
    boundary_margin = min((squared_distance(boundary[k], sites[j]) - r.square()).lo
                          for k in range(9) for j in range(11) if j not in (k, (k + 1) % 9))
    require(boundary_margin > 0, "boundary nearest-site separation failed")
    hull_margin = min(orient(sites[k], sites[(k + 1) % 9], sites[j]).lo
                      for k in range(9) for j in range(11) if j not in (k, (k + 1) % 9))
    require(hull_margin > 0, "ring is not a convex hull containing both hubs")
    counts = Counter(tuple(sorted((f[i], f[(i + 1) % 3]))) for f in FACES for i in range(3))
    hull = {tuple(sorted((k, (k + 1) % 9))) for k in range(9)}
    require(len(counts) == 21 and len(FACES) == 11 and
            all(n == (1 if edge in hull else 2) for edge, n in counts.items()),
            "invalid triangulation incidence")
    edges = sorted(counts)
    pair_count = 0
    for i, e in enumerate(edges):
        for f in edges[i + 1:]:
            pair_count += 1
            shared = set(e).intersection(f)
            if shared:
                v = next(iter(shared))
                a = next(k for k in e if k != v)
                b = next(k for k in f if k != v)
                z = orient(sites[v], sites[a], sites[b])
                dot = sum((sites[a][k] - sites[v][k]) * (sites[b][k] - sites[v][k])
                          for k in range(2))
                require(z.lo > 0 or z.hi < 0 or
                        (z.lo == 0 and z.hi == 0 and dot.hi < 0),
                        "edge pair direction unresolved")
            else:
                a, b, c, d = [sites[k] for k in (*e, *f)]
                z = [orient(a, b, c), orient(a, b, d), orient(c, d, a), orient(c, d, b)]
                separated = any((z[k].lo > 0 and z[k + 1].lo > 0) or
                                (z[k].hi < 0 and z[k + 1].hi < 0) for k in (0, 2))
                require(separated, "nonincident edge crossing or unresolved separation")
    site_face_count = 0
    for face in FACES:
        a, b, c = [sites[k] for k in face]
        sign = orient(a, b, c)
        require(sign.lo > 0 or sign.hi < 0, "degenerate listed face")
        for j in range(11):
            if j not in face:
                side = [orient(a, b, sites[j]), orient(b, c, sites[j]), orient(c, a, sites[j])]
                require(any(v.hi < 0 for v in side) if sign.lo > 0 else any(v.lo > 0 for v in side),
                        "site lies in listed closed triangle or separation unresolved")
                site_face_count += 1
    site_edge_count = 0
    for edge in edges:
        p, q = [sites[k] for k in edge]
        for j in range(11):
            if j not in edge:
                z = orient(p, q, sites[j])
                dot = sum((sites[j][k] - p[k]) * (sites[j][k] - q[k]) for k in range(2))
                require(z.lo > 0 or z.hi < 0 or dot.lo > 0,
                        "site on edge interior or separation unresolved")
                site_edge_count += 1
    face_rows = []
    empty_margin = D(100)
    slack_margin = D(100)
    # At the exact root, res5 and reflection prove seven fan and two
    # central faces have radius exactly r. Do NOT infer an equality merely
    # because an interval contains zero. These identities are described
    # explicitly in docs/N11_CHECK_SCOPE.md.
    for face in FACES:
        ring = [k for k in face if k < 9]
        if len(ring) == 1:
            center = (waist[0], waist[1] if ring[0] == 6 else -waist[1])
            radius2 = r.square()
            active = True
        else:
            edge = next(k for k in range(9) if set(ring) == {k, (k + 1) % 9})
            active = edge not in (0, 7)
            center = pins[edge] if active else circumcenter(sites, face)
            radius2 = r.square() if active else squared_distance(center, sites[face[0]])
            if not active:
                slack = (r.square() - radius2).lo
                require(slack > 0, "slack face radius exceeds root radius")
                slack_margin = min(slack_margin, slack)
        require((1 - squared_distance(center, (0, 0))).lo > 0, "Voronoi vertex outside unit disk")
        local_margin = min((squared_distance(center, sites[j]) - radius2).lo
                           for j in range(11) if j not in face)
        require(local_margin > 0, "empty circumcircle separation failed")
        empty_margin = min(empty_margin, local_margin)
        face_rows.append({"face": list(face), "active_identity": active,
                          "empty_margin_lower": str(local_margin)})
    return {"status": "PASS", "sites": [[v.record() for v in site] for site in sites],
            "face_count": len(FACES), "active_faces": 9, "slack_faces": 2,
            "edge_pairs_checked": pair_count, "empty_margin_lower": str(empty_margin),
            "site_face_pairs_checked": site_face_count, "site_edge_pairs_checked": site_edge_count,
            "slack_squared_radius_margin_lower": str(slack_margin),
            "boundary_margin_lower": str(boundary_margin), "faces": face_rows,
            "analytic_identities_required": "res5, reflection and arc-tile identities in N11_CHECK_SCOPE.md"}


def oracle_edges():
    """9 anchors, 11 site nodes, 11 face witnesses: the explicit 51-edge graph."""
    faces = [[9, k, k + 1] for k in range(4)]
    faces += [[10, k, (k + 1) % 9] for k in range(4, 9)]
    faces += [[9, 10, 0], [9, 10, 4]]
    edges = [e for k in range(9) for e in ((9 + k, k), (9 + k, (k - 1) % 9))]
    edges += [(9 + k, 20 + j) for j, face in enumerate(faces) for k in face]
    require(len(edges) == 51 and len(set(edges)) == 51, "bad oracle graph")
    return edges


def schur_field_check(field):
    """Re-derive each field by integer Bareiss elimination, not saved weights."""
    edges = oracle_edges()
    alpha = [F(x) for x in field["alpha"]]
    require(len(alpha) == 51 and min(alpha) > 0 and sum(alpha) == 1,
            "field is not a positive normalized 51-edge stress")
    scale = lcm(*(a.denominator for a in alpha))
    laplace = [[0 for _ in range(31)] for _ in range(31)]
    for (u, v), a in zip(edges, alpha):
        weight = a.numerator * (scale // a.denominator)
        laplace[u][u] += weight
        laplace[v][v] += weight
        laplace[u][v] -= weight
        laplace[v][u] -= weight
    # Augmented [L_ff | L_fa], 22 free nodes and 9 anchors.
    a = [row[9:] + row[:9] for row in laplace[9:]]
    prev = 1
    for k in range(21):
        pivot = a[k][k]
        require(pivot > 0, "free Laplacian positive-definite pivot failed")
        for i in range(k + 1, 22):
            factor = a[i][k]
            for j in range(k + 1, 31):
                numerator = pivot * a[i][j] - factor * a[k][j]
                require(numerator % prev == 0, "nonexact Bareiss division")
                a[i][j] = numerator // prev
            a[i][k] = 0
        prev = pivot
    det = a[-1][21]
    require(det > 0, "free Laplacian determinant must be positive")
    solution = [[0 for _ in range(9)] for _ in range(22)]
    for i in range(21, -1, -1):
        for j in range(9):
            numerator = a[i][22 + j] * det - sum(a[i][k] * solution[k][j] for k in range(i + 1, 22))
            require(numerator % a[i][i] == 0, "nonexact scaled back substitution")
            solution[i][j] = numerator // a[i][i]
    # The solve is checked against the ORIGINAL matrix, independently of
    # its elimination transcript. This identity is entirely integer exact.
    require(all(sum(laplace[9 + i][9 + k] * solution[k][j] for k in range(22)) ==
                det * laplace[9 + i][j] for i in range(22) for j in range(9)),
            "free-node exact linear solve failed")
    schur = [[laplace[i][j] * det - sum(laplace[i][9 + k] * solution[k][j] for k in range(22))
              for j in range(9)] for i in range(9)]
    require(all(schur[i][j] == schur[j][i] for i in range(9) for j in range(9)) and
            all(sum(row) == 0 for row in schur), "Schur symmetry/zero-row identity failed")
    expected = [(i, j, F(-schur[i][j], scale * det)) for i in range(9) for j in range(i + 1, 9)]
    require(all(w >= 0 for _, _, w in expected), "negative reduced-energy pair weight")
    saved = [(int(i), int(j), F(w)) for i, j, w in field["weights"]]
    require(saved == expected, "stored Schur weights differ from exact rederivation")
    return expected


def schur_checks(data, progress=None):
    require(data.get("schema") == "n11-exact-schur-fields-v1", "wrong Schur field schema")
    fields = data["fields"]
    require(len(fields) == 371, "all 371 fields are required")
    require(len({field["name"] for field in fields}) == 371, "Schur field names must be unique")
    names = []
    for i, field in enumerate(fields):
        schur_field_check(field)
        names.append(field["name"])
        if progress and ((i + 1) % 50 == 0 or i + 1 == len(fields)):
            progress(f"n11: exact Schur fields {i + 1}/{len(fields)}")
    bad = dict(fields[0])
    bad["weights"] = [list(row) for row in fields[0]["weights"]]
    bad["weights"][0][2] = str(F(bad["weights"][0][2]) + F(1, 10 ** 40))
    rejected = False
    try:
        schur_field_check(bad)
    except ValueError:
        rejected = True
    require(rejected, "corrupted-weight negative control unexpectedly passed")
    return {"status": "PASS", "field_count": len(fields), "edges": 51, "free_nodes": 22,
            "pair_weights_recomputed": 36 * len(fields), "negative_control_rejected": True,
            "scope": "positive normalized stresses and exact Schur energy identity; no terminal angular leaf inequality"}


def run_checks(data_dir=None, progress=None):
    """Return scoped results; raise ValueError on any arithmetic failure."""
    start = time.perf_counter()
    directory = Path(data_dir) if data_dir is not None else DEFAULT_DATA
    source = directory / "root_input.json"
    data = json.loads(source.read_text(encoding="utf-8"))
    if progress:
        progress("n11: recomputing 12-dimensional root inclusion and threshold")
    box, root = root_check(data)
    if progress:
        progress("n11: recomputing attaining-configuration interval geometry")
    geometry = geometry_check(box)
    field_source = directory / "schur_fields.json"
    if progress:
        progress("n11: rederiving all positive-stress Schur fields by exact integer arithmetic")
    fields = schur_checks(json.loads(field_source.read_text(encoding="utf-8")), progress)
    return {"n": 11, "status": "SCOPED_PASS", "full_global_proof_replayed": False,
            "verified": {"root": root, "attainment_geometry": geometry, "schur_fields": fields},
            "not_replayed": ["two-circle C450 full 36-interval capacity certificate",
                             "all seven metric graph-class exclusions",
                             "2386 energy leaves and 120 local leaves of the global oracle",
                             "unrestricted analytic geometry/topology reduction"],
            "root_input_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "schur_fields_sha256": hashlib.sha256(field_source.read_bytes()).hexdigest(),
            "seconds": round(time.perf_counter() - start, 3)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--json", action="store_true", help="print complete JSON report")
    parser.add_argument("--report", type=Path, help="write complete JSON report")
    args = parser.parse_args(argv)
    try:
        result = run_checks(args.data_dir, None if args.json else lambda x: print(x, flush=True))
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError) as exc:
        print(json.dumps({"n": 11, "status": "FAIL", "error": str(exc)}))
        return 1
    text = json.dumps(result, indent=2)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(text + "\n", encoding="utf-8")
    if args.json:
        print(text)
    else:
        print("n11 SCOPED_PASS: root, same-root threshold, attainment geometry and all 371 Schur fields")
        print("Full global lower-bound proof NOT replayed; see docs/N11_CHECK_SCOPE.md.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
