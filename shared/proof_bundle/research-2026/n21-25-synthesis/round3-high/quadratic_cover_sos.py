"""Exact sparse quadratic -> single quartic compilation for FULL disk graphs.

This is a feasibility encoding, not an infeasibility SOS certificate or an
implemented quantifier-elimination backend. A polynomial zero does not pay
optimality without excluding all competing models at strictly smaller t.
"""
from fractions import Fraction as F
from math import gcd
from cross_order_strict_transfer import validate_disk

assert __debug__


def clean(poly):
    return {key: F(value) for key, value in poly.items() if value}


def constant(value):
    return {} if value == 0 else {(): F(value)}


def variable(index):
    return {(index,): F(1)}


def add(*polys):
    result = {}
    for poly in polys:
        for monomial, value in poly.items():
            result[monomial] = result.get(monomial, F(0))+value
    return clean(result)


def scaled(poly, value):
    return clean({key: coefficient*value for key, coefficient in poly.items()})


def mul(first, last):
    result = {}
    for a, x in first.items():
        for b, y in last.items():
            key = tuple(sorted(a+b))
            result[key] = result.get(key, F(0))+x*y
    return clean(result)


def square(poly):
    return mul(poly, poly)


def derivative(poly, index):
    result = {}
    for monomial, value in poly.items():
        power = monomial.count(index)
        if power:
            rest = list(monomial)
            rest.remove(index)
            key = tuple(rest)
            result[key] = result.get(key, F(0))+power*value
    return clean(result)


def primitive_integer(poly):
    common = 1
    for value in poly.values():
        common = common*value.denominator//gcd(common, value.denominator)
    integers = {key: int(value*common) for key, value in poly.items()}
    divisor = 0
    for value in integers.values():
        divisor = gcd(divisor, abs(value))
    assert divisor > 0
    # Only positive scaling; in particular inequality signs are preserved.
    return {key: F(value//divisor) for key, value in integers.items()}


def build(N, B, masks, upper, opposite_anchor):
    validate_disk(N, B, masks)
    assert 1 <= opposite_anchor < B and 0 < F(upper) < F(1, 3)
    faces = [[j for j in range(N) if mask >> j & 1] for mask in masks]
    V = B+N+len(faces)
    G = 2*(V-1)
    t = variable(G)
    points = [(constant(1), constant(0))]
    points += [(variable(2*(i-1)), variable(2*(i-1)+1)) for i in range(1, V)]
    def norm(i):
        return add(square(points[i][0]), square(points[i][1]))
    def distance(u, v):
        return add(*(square(add(points[u][axis], scaled(points[v][axis], -1)))
                     for axis in (0, 1)))
    equalities = []
    inequalities = []
    for i in range(1, B):
        equalities.append((f"unit-anchor-{i}", add(norm(i), constant(-1))))
    rods = [(i, B+i) for i in range(B)]+[(i, B+(i+1) % B) for i in range(B)]
    rods += [(B+N+f, B+j) for f, face in enumerate(faces) for j in face]
    for i, (u, v) in enumerate(rods):
        inequalities.append((f"rod-{i}-{u}-{v}", add(t, scaled(distance(u, v), -1))))
    for i in range(B, V):
        inequalities.append((f"unit-disk-free-node-{i}", add(constant(1), scaled(norm(i), -1))))
    for i in range(B):
        j = (i+1) % B
        inequalities.append((f"positive-anchor-order-{i}",
                             add(mul(points[i][0], points[j][1]),
                                 scaled(mul(points[i][1], points[j][0]), -1))))
    inequalities += [
        ("some-anchor-in-opposite-halfplane", scaled(points[opposite_anchor][0], -1)),
        ("nonnegative-radius-square", t),
        ("radius-square-upper-bound", add(constant(F(upper)**2), scaled(t, -1))),
    ]
    equalities = [(name, primitive_integer(poly)) for name, poly in equalities]
    inequalities = [(name, primitive_integer(poly)) for name, poly in inequalities]
    assert all(max(map(len, poly), default=0) <= 2 for _, poly in equalities+inequalities)
    residuals = [poly for _, poly in equalities]
    slack_indices = []
    for j, (_, poly) in enumerate(inequalities):
        index = G+1+j
        slack_indices.append(index)
        residuals.append(add(poly, scaled(square(variable(index)), -1)))
    compiled = add(*(square(poly) for poly in residuals))
    assert max(map(len, compiled)) <= 4
    assert all(value.denominator == 1 for value in compiled.values())
    return {"N": N, "B": B, "V": V, "G": G, "radius_square_index": G,
            "faces": faces, "face_masks": masks, "rods": rods,
            "opposite_anchor": opposite_anchor, "radius_upper": str(F(upper)),
            "equalities": equalities, "inequalities": inequalities,
            "slack_indices": slack_indices, "residuals": residuals, "F": compiled,
            "total_variables": G+1+len(inequalities)}


def serialize(poly):
    return [{"variables": list(monomial), "coefficient": str(value)}
            for monomial, value in sorted(poly.items())]


def gradient_identity(model):
    """Compare every formal derivative with the exact sum-of-squares rule."""
    compiled = model["F"]
    for index in range(model["total_variables"]):
        expected = add(*(scaled(mul(poly, derivative(poly, index)), 2)
                         for poly in model["residuals"]))
        assert derivative(compiled, index) == expected
    return True
