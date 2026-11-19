# SPDX-License-Identifier: MIT
"""Exact optima with analytic lower and matching upper proofs for n <= 4.

This module reports written proofs, not Lean or kernel-checked proofs.
It refuses to claim an optimum for any unimplemented order.
"""

_CASES = {
    1: ("1", "1", (("0", "0"),)),
    2: ("1", "1", (("0", "0"), ("0", "0"))),
    3: ("sqrt(3)/2", "3/4", (("1/2", "0"),
                             ("-1/4", "sqrt(3)/4"),
                             ("-1/4", "-sqrt(3)/4"))),
    4: ("sqrt(2)/2", "1/2", (("sqrt(2)/2", "0"),
                             ("0", "sqrt(2)/2"),
                             ("-sqrt(2)/2", "0"),
                             ("0", "-sqrt(2)/2"))),
}

_DIAMETER = (
    "A disk containing opposite points of the unit circle has radius at "
    "least 1 by the triangle inequality."
)
_ARC = (
    "It suffices to consider radii r<1. A covering disk centered at distance "
    "d>0 from the origin captures the directions whose angle from its center "
    "direction has cosine at least (1+d^2-r^2)/(2d). This threshold is at least "
    "sqrt(1-r^2), by (d-sqrt(1-r^2))^2>=0. Thus it covers an arc of length "
    "at most 2 asin(r), including the empty and tangent cases. A disk "
    "centered at the origin covers no boundary point for r<1. Covering the "
    "whole boundary forces 2n asin(r)>=2 pi, so r>=sin(pi/n)."
)
_SECTOR = (
    "Set alpha=pi/n and put the centers at distance cos(alpha) on equally "
    "spaced rays. A point at distance s in [0,1] in its nearest ray sector "
    "has angular offset |theta|<=alpha. Its squared distance to that center "
    "is s^2-2s cos(alpha) cos(theta)+cos(alpha)^2, convex in s. Its endpoint "
    "values at 0 and 1 are respectively cos(alpha)^2 and at most "
    "sin(alpha)^2. Since cos(alpha)<=sin(alpha) for n=2,3,4, the entire "
    "closed sector is covered at radius sin(alpha)."
)


def solve_global(n: int) -> dict | None:
    """Return an exact proof-backed output for n=1–4, or None for n=5–22."""
    if type(n) is not int or not 1 <= n <= 22:
        raise ValueError("n must be an integer in 1..22")
    if n not in _CASES:
        return None
    radius, squared, centers = _CASES[n]
    return {
        "n": n, "status": "exact_global", "radius_exact": radius,
        "radius_squared": squared, "centers": [list(c) for c in centers],
        "proof": {
            "kind": "analytic",
            "lower": _DIAMETER if n == 1 else _ARC,
            "upper": "The unit disk at the origin attains radius 1."
                     if n == 1 else _SECTOR,
        },
    }
