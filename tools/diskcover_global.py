# SPDX-License-Identifier: MIT
"""Exact optima with analytic lower and matching upper proofs for n = 1–4 and 7–10.

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

for _b in (7, 8, 9):
    _radius = "sqrt(2)-1" if _b == 8 else f"1/(1+2*cos(2*pi/{_b}))"
    _d = f"pi/{_b}"
    _rho = f"2*({_radius})*cos({_d})"
    _CASES[_b+1] = (
        _radius, f"({_radius})^2",
        (("0", "0"),) + tuple(
            (f"{_rho}*cos(2*pi*{i}/{_b})", f"{_rho}*sin(2*pi*{i}/{_b})")
            for i in range(_b)
        ),
    )


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


_RING_LOWER = (
    "Write b=n-1, d=pi/b, U=1/(4*cos(d)^2-1), and suppose radius r<U "
    "suffices. For every center c with norm above sqrt(1-U^2), set "
    "lambda=(1-U^2)/norm(c)^2 and replace c by lambda*c. For norm(x)<=1, "
    "dist(x,lambda*c)^2-U^2 = lambda*(dist(x,c)^2-U^2) "
    "+(1-lambda)*(norm(x)^2-1). Thus strict coverage persists. By "
    "compactness and continuity all centers can be moved strictly inside "
    "norm=sqrt(1-U^2) and put in general position while retaining strict "
    "coverage: centers distinct, no three collinear, no four cocircular, "
    "and no triple nearest-center ties on the unit circle. Each bisector "
    "is closer than sqrt(1-U^2) to the origin (its signed coordinate is "
    "the projection of the midpoint), so its unit-circle chord exceeds "
    "2U in length. A nearest-center cell on the circle is contained in "
    "the short arc cut out by its radius-U disk. If two points of that "
    "arc belong to the cell but some point between them does not, one "
    "competitor's bisector would cross the intervening arc twice, with "
    "both endpoints inside the radius-U disk, a contradiction. Positive "
    "length ownership arcs are therefore connected and partition the circle. "
    "Their half-angles t_i sum to pi and are at most asin(U) by the arc bound. "
    "Since U<sin(pi/(b-1)), at least b disks own arcs. As U<1/2, the disk "
    "covering the origin cannot own an arc; exactly b owners and one "
    "interior center z remain. "
    "For two nonadjacent owners, go along the shorter direction between "
    "their arc midpoints and take the two far endpoints of their arcs. "
    "If their separation along this path is 2*sigma, it spans at least "
    "three complete arcs, and pi-(b-3)*T <= sigma <= pi/2+T, where "
    "T=463/1000 for b=7 and T=428/1000 for b=8. For b=7, U<4451/10000, "
    "sin(T)>446/1000, sin(pi-4*T)>95/100, and cos(T)>894/1000. For b=8, "
    "U<4143/10000, sin(T)>415/1000, sin(pi-5*T)>84/100, and cos(T)>90/100. "
    "These rational inequalities follow from 3.14159<pi<3.14160 and "
    "alternating sine and cosine Taylor bounds through degree ten "
    "(reduce sin(pi-k*T) to sin(k*T)). Thus T>asin(U), and sin(sigma)>2U "
    "by concavity of sine on the stated interval. The far endpoints "
    "are more than 4U apart; hence their centers are more than 2U apart. "
    "At a boundary switch the two adjacent owners share a truncated "
    "Voronoi edge running inward. Its other endpoint cannot be on the "
    "unit circle, by the bisector chord bound. At its interior endpoint "
    "three centers meet. A third boundary owner would be nonadjacent "
    "to at least one of the first two, impossible since their common "
    "witness has distance less than U from each. The third center is z. "
    "Around the bounded convex Voronoi cell of z, the outward normals "
    "are consecutive vectors p_i-z. Thus the angles gamma_i in (0,pi) "
    "of these triangles at z sum to 2*pi. Each circumradius is <U; "
    "by the sine law and concavity the perimeter P of the closed owner "
    "walk satisfies P<2*U*b*sin(2*pi/b). "
    "Conversely, let H(v)=max_i dot(p_i,v). Projecting the closed walk "
    "onto v gives total variation at least 2*(H(v)+H(-v)). Integration "
    "over a half-turn gives P>=integral(H) over a full turn, since each "
    "segment projects with integrated absolute length twice its length. "
    "On its own arc the owner lies at radial component at least "
    "cos(t)-sqrt(U^2-sin(t)^2), by averaging squared distances to its "
    "two endpoints. Integrating dot(p_i,v) on the arc therefore gives "
    "at least 2*(t-G(t)), for G(t)=t-sin(t)*cos(t)+sin(t)*sqrt(U^2-sin(t)^2). "
    "For s=sin(t), c=cos(t), h=sqrt(U^2-s^2), direct differentiation "
    "gives h^3*G''/s=4*c*h^3-U^4-3*U^2+6*U^2*s^2+2*s^2-4*s^4. "
    "Using c*h^3<=U*(U^2-s^2), drop the term -4*s^4 and bound the remaining "
    "linear term above at s^2=U^2, since 2-4*U+6*U^2 is positive. "
    "This gives at most U^2*(5*U^2-1)<0. "
    "Consequently Jensen gives P>=2*b*sin(d)*(cos(d)-sqrt(U^2-sin(d)^2)). "
    "Since 2*U*cos(d)<cos(d) and solves the endpoint distance equation "
    "a^2-2*a*cos(d)+1=U^2, the factor in parentheses equals 2*U*cos(d). "
    "The resulting lower bound equals the strict upper bound, impossible."
)
_RING_UPPER = (
    "Put one center at the origin and b equally spaced centers at "
    "distance 2*U*cos(pi/b), where U=1/(4*cos(pi/b)^2-1). The origin disk "
    "covers norms through U. In each ring center's sector the half-angle "
    "is at most d=pi/b. At s=U and s=1 the worst squared distances to "
    "that center occur at angle d and both equal U^2 on substitution. "
    "Convexity in s covers the radial interval between these endpoints."
)


def solve_global(n: int) -> dict | None:
    """Return a proof for n=1–4 or 7–10, or None for the other supported orders."""
    if type(n) is not int or not 1 <= n <= 22:
        raise ValueError("n must be an integer in 1..22")
    if n not in _CASES:
        return None
    radius, squared, centers = _CASES[n]
    if n == 10:
        from diskcover_n10_area import check_n10_area, check_n10_eight_owner
        return {
            "n": 10, "status": "exact_global", "radius_exact": radius,
            "radius_squared": squared, "centers": [list(c) for c in centers],
            "proof": {
                "kind": "analytic_with_directed_arithmetic",
                "lower": (
                    "Assuming a smaller radius, normalize the strict cover and classify "
                    "its boundary owners. Fewer than eight cannot cover the boundary; "
                    "eight are excluded by the inward-pair distance obstruction. Nine "
                    "owners with outer triples are excluded by the two area comparisons; "
                    "the remaining wheel contradicts the strict perimeter bound."
                ),
                "upper": _RING_UPPER,
                "documents": [
                    "docs/DISKCOVER_CLASSICAL_N10.md",
                    "docs/DISKCOVER_N10_EIGHT_OWNERS.md",
                    "docs/DISKCOVER_N10_OUTER_JUNCTIONS.md",
                ],
                "directed_checks": [check_n10_area(), check_n10_eight_owner()],
            },
        }
    return {
        "n": n, "status": "exact_global", "radius_exact": radius,
        "radius_squared": squared, "centers": [list(c) for c in centers],
        "proof": {
            "kind": "analytic",
            "lower": {1: _DIAMETER, 7: _SEVEN_LOWER,
                      8: _RING_LOWER + " " + _ARC,
                      9: _RING_LOWER + " " + _ARC}.get(n, _ARC),
            "upper": "The unit disk at the origin attains radius 1."
                     if n == 1 else {7: _SEVEN_UPPER, 8: _RING_UPPER, 9: _RING_UPPER}.get(n, _SECTOR),
        },
    }
