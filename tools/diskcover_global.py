# SPDX-License-Identifier: MIT
"""Exact optima with analytic lower and matching upper proofs for n = 1–4 and 7.

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
    7: ("1/2", "1/4", (("0", "0"),
                        ("sqrt(3)/2", "0"), ("sqrt(3)/4", "3/4"),
                        ("-sqrt(3)/4", "3/4"), ("-sqrt(3)/2", "0"),
                        ("-sqrt(3)/4", "-3/4"), ("sqrt(3)/4", "-3/4"))),
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


_SEVEN_LOWER = (
    "At any r<1/2, a covering disk containing the origin cannot touch the "
    "unit circumference: its center norm is at most r, so every point it "
    "covers has norm at most 2r<1. Each of the other six disks has angular "
    "footprint at most 2 asin(r), strictly less than pi/3, by the boundary "
    "arc estimate. The six footprints cannot cover 2 pi. " + _ARC
)
_SEVEN_UPPER = (
    "Take the origin and six centers at distance sqrt(3)/2 in directions "
    "spaced by pi/3. The origin disk covers points of norm at most 1/2. "
    "For a point of norm s in [1/2,1], an outer center has angular offset "
    "at most pi/6. Its squared distance is at most s^2+3/4-3s/2, a convex "
    "function with value 1/4 at both endpoints. Thus radius 1/2 suffices."
)


def solve_global(n: int) -> dict | None:
    """Return a proof for n=1–4 or 7, or None for the other supported orders."""
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
            "lower": {1: _DIAMETER, 7: _SEVEN_LOWER}.get(n, _ARC),
            "upper": "The unit disk at the origin attains radius 1."
                     if n == 1 else _SEVEN_UPPER if n == 7 else _SECTOR,
        },
    }
