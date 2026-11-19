<!-- SPDX-License-Identifier: MIT -->
# n=13: native reductions and remaining exact obligations

The target is the minimum common radius for 13 disks covering the **closed**
unit disk, with unrestricted centers. This note proves reductions, not the
matching global lower bound or an attaining configuration.

## Reference candidate and archived work

The [pinned external source](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover13/README.md)
defines the proposed radius as the square root of the radius-squared coordinate
of a 119-variable isolated root in its rational Krawczyk box. Its display begins
`0.34664545692738964`. It is a reference, not a premise for the native lower
bound. The external runner claims to check the candidate tree and noncandidate
cases; running the author's package would not supply a fresh native proof.

The [native n13 audit](../cover21/proof_bundle/research-2026/n21-global/evidence/milestone-v1-archive/research-2026/n13-global/independent_checks.py)
(SHA-256 `76431ce80cd316ea6a31d4fda85b8a099ae5e6d5f3eeef202254b14dff499377`)
rebuilds a 62-dimensional positive-definite matrix by exact Bareiss elimination
and implements separate fixed-point trigonometric enclosures, but reuses the
external certificates and tree/force kernels. It was not rerun here. The
[n27 archive manifest](../cover27/proof_bundle/research-2026-11/core-search/MANIFEST.json)
records a weaker n13 lower bound of `0.3385`; the manifest does not prove it,
and this note does not promote it to a freshly checked bound. The historical
[n13/14/15 candidate profile](../cover14/proof_bundle/research-2026/next-cover-global/members/candidate/REPORT-n13-14-15.md)
suggests ten boundary-active disks and no symmetry for the n13 candidate; this
is numerical evidence, not a restriction on arbitrary covers.

## Exact reduction: 9–12 boundary-reaching disks

For every cover of radius `r <= 7/20`, at least 9 but at most 12 disks meet the
target circle. Indeed a center of norm `d > 0` covers a circular arc of angle
at most `2 asin(r)`: writing the half-angle as `alpha`, the cosine rule
gives
`cos(alpha) = (d² + 1 - r²)/(2d) >= sqrt(1-r²)`
whenever the disk reaches the boundary. An origin-centered disk does not reach
it. The strict threshold `7/20 < sin(pi/8)` follows from
`sin²(pi/8) = (2-sqrt(2))/4` and the rational comparison
`(151/100)^2 > 2`. Eight such arcs therefore have total length strictly
less than the circumference, even if tangencies and overlaps are counted.
Conversely, a disk covering the origin has center norm at most `r` and
cannot touch the unit circle when `2r < 1`. This excludes 13 boundary-reaching
disks even when some centers coincide.

Reproduce the nontrigonometric arithmetic used in these two cuts:

```sh
python - <<'PY'
from fractions import Fraction as Q
r = Q(7, 20)
assert 2*r < 1
assert 2-4*r*r == Q(151, 100) > 0
assert (2-4*r*r)**2 > 2
print("n13 boundary-count rational comparisons passed")
PY
```

Remaining branch counts are 9, 10, 11 and 12. Reaching the circle includes
tangency; the count must not be conflated with arcs that receive a positive
portion of a chosen boundary partition.

## Finite exact verifier for any proposed centers

Project centers radially to the closed unit disk: orthogonal projection onto
this convex disk cannot increase their distance to a target point. Measure the
boundary count after projection; the reduction does not require preserving
the original count. Discard
duplicate centers for verification and keep the declared multiplicity for the
branch count. For each distinct center c, intersect its closed Voronoi cell
(the half-planes `2(d-c)·x <= |d|²-|c|²` over the other centers d) with
the target disk. The radius of a fixed configuration is the maximum, over these
clipped cells, of the maximum of `|x-c|` in the cell. A finite test checks only:

1. Intersections of two nonparallel bisectors bounding the cell, if feasible
   in the cell and disk.
2. Intersections of each such bisector with the unit circle, if feasible in the
   cell.
3. The antipode `-c/|c|` if c is nonzero and this
   antipode belongs to the clipped cell. For c=0 also test the fixed circle
   point (1,0) if it belongs to the cell.

To see completeness, a maximum in the interior of the disk cannot be interior
to a cell: squared distance is strictly convex in every line direction.
A maximum on a straight face is attained at an endpoint, whose distance is
at least that of any interior point of the face. The endpoint is a vertex or
a circle intersection. On a nondegenerate circular arc, the squared distance
is `1+|c|²-2c·x`; the only possible interior maximizing point for nonzero c
is its antipode. With c=0 the arc is constant, so its endpoints suffice unless
the entire circle is feasible; that case is covered by (1,0). Isolated feasible
circle points come from bisector intersections or tangency. These tests cover
ties, parallel bisectors (intersect only nonparallel pairs), and the
one-distinct-center case. Feasibility and squared distances can be checked
exactly over real algebraic coordinates without boundary sampling.

This separates two missing tasks: (a) provide and certify native attaining
centers at the reference root (the finite test is a sufficient exact
acceptance condition); (b) exclude every smaller radius in **all four**
arbitrary-center branches. In (b), center variables may be confined to the
closed unit disk by projection, but symmetry and candidate topology may not be
assumed. The clipped-cell tests offer an exact semialgebraic route, not a claim
that it is tractable without additional branch reductions. No global verdict
is inferred from the candidate profile, archived manifest, or this arithmetic.
