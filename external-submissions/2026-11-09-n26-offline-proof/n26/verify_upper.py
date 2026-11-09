"""Exact closed-unit-disk coverage verification using only the standard library."""

import argparse
import json
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


def norm2(a):
    return dot(a, a)


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def mul(t, a):
    return t * a[0], t * a[1]


def sgn(t):
    return (t > 0) - (t < 0)


def sign_radical(a, b, d):
    """Sign of a + b sqrt(d), with rational a, b and d >= 0."""
    if b == 0 or d == 0:
        return sgn(a)
    if a == 0 or sgn(a) == sgn(b):
        return sgn(b)
    return sgn(a) * sgn(a * a - b * b * d)


def verify(points, radius):
    if len(points) != 26 or radius <= 0:
        raise ValueError("Expected 26 centers and a positive radius")
    sites = list(dict.fromkeys(points))
    squared = [norm2(p) for p in sites]
    limit = radius * radius
    count = {"interior": 0, "circle_line": 0, "circle_stationary": 0}

    for i, p in enumerate(sites):
        # A cell inequality is n dot x <= h.
        halfplanes = [
            (sub(q, p), (squared[j] - squared[i]) / 2)
            for j, q in enumerate(sites)
            if j != i
        ]

        def check_rational(x):
            if any(dot(n, x) > h for n, h in halfplanes):
                return
            count["interior"] += 1
            if norm2(sub(x, p)) > limit:
                raise ValueError(f"Uncovered line vertex in cell {i}: {x}")

        def check_circle(a, b, d, kind):
            # Point on the circle is a + b sqrt(d).
            if any(
                sign_radical(dot(n, a) - h, dot(n, b), d) > 0
                for n, h in halfplanes
            ):
                return
            count[kind] += 1
            # On the circle, |x-p|^2 = 1 + |p|^2 - 2 p dot x.
            if sign_radical(
                1 + squared[i] - 2 * dot(p, a) - limit, -2 * dot(p, b), d
            ) > 0:
                raise ValueError(f"Uncovered {kind} point in cell {i}: {a}, {b}, {d}")

        for (n, h), (m, g) in combinations(halfplanes, 2):
            det = n[0] * m[1] - n[1] * m[0]
            if det:
                x = ((h * m[1] - g * n[1]) / det, (g * n[0] - h * m[0]) / det)
                if norm2(x) <= 1:
                    check_rational(x)

        for n, h in halfplanes:
            n2 = norm2(n)
            d = (n2 - h * h) / (n2 * n2)
            if d >= 0:
                a = mul(h / n2, n)
                b = -n[1], n[0]
                check_circle(a, b, d, "circle_line")
                if d:
                    check_circle(a, mul(-1, b), d, "circle_line")

        zero = Q(0), Q(0)
        if squared[i]:
            check_circle(zero, p, 1 / squared[i], "circle_stationary")
            check_circle(zero, mul(-1, p), 1 / squared[i], "circle_stationary")
        else:
            check_circle((Q(1), Q(0)), zero, Q(0), "circle_stationary")
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--radius", help="Override the radius with an exact rational")
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text(encoding="utf-8"))
    points = [tuple(Q(x) for x in p) for p in data["centers"]]
    radius = Q(args.radius or data["radius"])
    count = verify(points, radius)
    print(f"PASS  U = {radius}  ({float(radius):.16g})")
    print("Feasible candidate checks by cell:", count)


if __name__ == "__main__":
    main()
