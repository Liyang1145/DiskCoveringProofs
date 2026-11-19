<!-- SPDX-License-Identifier: MIT -->
# n=13: native reductions and remaining exact obligations

The target is the minimum common radius for 13 disks covering the **closed**
unit disk, with unrestricted centers. This note proves reductions and an independently checked attaining configuration
at the candidate algebraic radius. It does not prove the matching global lower bound.

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

The initial possible counts are 9, 10, 11 and 12. Reaching the circle includes
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

The independent upper replay below certifies an attaining configuration at the
reference root. To obtain global exactness one still needs to exclude every smaller
radius in the remaining arbitrary-center branches. The twelve-owner branch is
excluded below. In the other branches, center variables may be confined to the
closed unit disk by projection, but symmetry and candidate topology may not be
assumed. The clipped-cell tests offer an exact semialgebraic route, not a claim
that it is tractable without additional branch reductions. No global verdict
is inferred from the candidate profile, archived manifest, or this arithmetic.

## New branch exclusion at \(U=0.346646\): twelve boundary owners

Assume a cover at radius \(r<U=173323/500000\). All target points are
strictly covered by radius-\(U\) disks at the same centers. Suppose there are
twelve boundary owners (centers whose nearest-center cells have positive
boundary arcs), and let \(z\) be the thirteenth center. The twelve outer
centers have norms \(>1-U\), so none covers the origin at radius \(U\).
Thus \(s=|z|<U\). The entire circle of radius \(U\) about \(z\) lies inside the
target and must be strictly covered by outer disks, since its points have
distance exactly \(U\) from \(z\). At the circle point on the side opposite
\(z\) (any point if \(z=0\)), the norm is \(U-s\). Its distance from every
outer center is greater than \(1-2U+s\); hence \(s<3U-1<.04\).

Write \(\alpha,\beta\) for the maximum half-angles covered by any one outer
radius-\(U\) disk on the unit circumference and the radius-\(U\) circle about
\(z\) respectively, with zero for a missing footprint. Both whole circles
are covered by the twelve outer disks, so \(\sum\alpha,\sum\beta\ge\pi\).
We bound \(\alpha+(9/25)\beta\) disk by disk.

If \(\beta=0\), the boundary angular footprint estimate gives
\(\alpha\le\arcsin U<.355\). Otherwise put \(d=|c-z|\), where \(c\) is the
outer center. Then \(d>1-U-s>.613\), \(d\le2U<.694\), and
\(\cos\beta=d/(2U)\). Its norm \(D=|c|\) obeys \(D<d+.04\le.734\).
For \(D<\sqrt{1-U^2}\) the quantity \((1+D^2-U^2)/(2D)\)
decreases with \(D\). Therefore on each interval
\([\ell,h]\) in the following rational table, the cosine rule gives
\(\alpha\le a\), \(\beta\le b\).

| \(\ell\) | \(h\) | \(a\) | \(b\) |
|---:|---:|---:|---:|
| .613 | .625 | .110 | .487 |
| .625 | .635 | .148 | .449 |
| .635 | .645 | .176 | .414 |
| .645 | .655 | .199 | .377 |
| .655 | .665 | .218 | .335 |
| .665 | .675 | .235 | .288 |
| .675 | .685 | .250 | .231 |
| .685 | .694 | .261 | .156 |

Every row has \(a+(9/25)b<.355\). Altogether,
\[
 (34/25)\pi\ \le\ \sum\bigl(\alpha+(9/25)\beta\bigr)
 <12(.355)=4.26<(34/25)\pi ,
\]
a contradiction. This excludes exactly twelve boundary owners, without any
assumption of a centered or symmetric inner disk.

### Additional native pruning for the surviving owner cases

For the normalized generic nearest-center partition, one can forbid long
edges between outer owners. The normalization at test radius \(U<1\)
replaces a center \(c\) with \(\lambda c\) when \(|c|>\sqrt{1-U^2}\),
where \(\lambda=(1-U^2)/|c|^2\); the identity
\[
 |x-\lambda c|^2-U^2=\lambda(|x-c|^2-U^2)
 +(1-\lambda)(|x|^2-1)
\]
preserves strict coverage. Use the strict margin to lower all center norms
below \(\sqrt{1-U^2}\) and avoid degeneracies. A pair bisector intersects
the unit circle in a chord longer than \(2U\); as two crossings inside a
single disk would be closer than \(2U\), any positive ownership arc is
connected. Let \(B\) be the number of owners, cyclically ordered.
Take any two whose cyclic index separation is at least \(B-7\)
in both directions (with \(B=9,10,11\)). Follow the shorter direction
between their arc midpoints and extend at both ends to the far arc
endpoints. If the resulting endpoint angular interval has length \(2\sigma\),
there are at least \(B-6\) complete arcs along it, and each half-angle is
below \(T=.355\). It follows that
\(\pi-6T\le\sigma\le\pi/2+T\).
The sine on this entire interval is above \(2U\), since both endpoint
values are above \(2U\) and sine is concave there. The far endpoints
are therefore more than \(4U\) apart, so their centers are more than
\(2U\) apart by the triangle inequality. They cannot share a point
within radius \(U\), hence cannot be connected in the clipped Voronoi
dual. In particular:

- With 9 outer owners, every outer chord is forbidden.
- With 10 outer owners, only chords of cyclic separation 2 are possible.
- With 11 outer owners, only chords of separation 2 or 3 are possible.

These are reductions, not exclusions of the remaining three branches.

### Exact arithmetic replay for the new reductions

All trigonometric comparisons admit elementary alternating-series enclosures.
This script checks the table and the bounds used above; the geometry is
the written argument, not an output of the script.

```sh
python - <<'PY'
from fractions import Fraction as F
U,T=F(173323,500000),F('.355')
sin_lo=lambda x: x-x**3/6+x**5/120-x**7/5040
cos_lo=lambda x: 1-x*x/2
cos_hi=lambda x: 1-x*x/2+x**4/24
assert sin_lo(T)>U and cos_lo(T)>2*U and sin_lo(6*T)>2*U
assert 3*U-1<F('.04') and 1-U-F('.04')>F('.613')
assert 2*U<F('.694') and F('.734')**2 < 1-U**2
for l,h,a,b in [
    (613,625,110,487),(625,635,148,449),(635,645,176,414),
    (645,655,199,377),(655,665,218,335),(665,675,235,288),
    (675,685,250,231),(685,694,261,156),
]:
    l,h,a,b=map(lambda k:F(k,1000),(l,h,a,b))
    D=h+F('.04')
    assert cos_hi(a)<(1+D*D-U*U)/(2*D)
    assert cos_hi(b)<l/(2*U)
    assert a+F(9,25)*b<T
assert 12*T<F(34,25)*F('3.14')
print("n13 twelve-owner exclusion and long-chord arithmetic passed")
PY
```

## Independent exact attaining configuration at the algebraic candidate

Run:

```sh
python tools/check_native_n13_root.py
python tools/diskcover_n13_upper.py
```

The first command proves existence of a real algebraic radius \(r_*=\sqrt{t_*}\)
in \((0.346645456927389643467869738193878789537187452966783984053969,
0.346645456927389643467869738193878789537187452966783984053970)\) and a full
cover at that radius. The 119-variable rational input in
[`verification/n13/candidate_midpoint.json`](../verification/n13/candidate_midpoint.json)
contains only the midpoint and box radius extracted from the pinned upstream
candidate certificate, whose SHA-256 is
`d7f5d30fbeb1196f4232b6b7cc2509c67bdaf48cbd969389459c91e58dc360ee`.
In particular the replay does not use the upstream approximate inverse,
geometry routines, proof trees or verdicts.

The checker independently constructs the forty-seven equations
\(|z_u-z_v|^2=t\) for the listed contacts, nine unit anchor equations,
and sixty-three stationarity equations of their Lagrangian with objective
\(t\). At the rational midpoint \(m\) it constructs \(J=DF(m)\) and
finds a proposed inverse \(Y\) by decimal elimination. Nothing depends on
the accuracy of decimal arithmetic: with \(\varepsilon=10^{-65}\) and
\(b_i\) the checker’s sum of absolute Hessian bounds for component \(i\),
every row is certified by exact rational arithmetic to satisfy
\[
 \frac{|(YF(m))_i|}{\varepsilon}
 +\sum_j |(I-YJ)_{ij}|+\varepsilon\sum_j |Y_{ij}|b_j<1.
\]
The last term bounds infinity-norm row variation of \(YDF\) throughout
the box from the monomial coefficients. This simultaneously gives strict
inclusion and contraction of \(x\mapsto x-YF(x)\). Since \(I-YJ\) has norm
below one, \(YJ\), hence \(Y\), is invertible; the unique fixed point in
the box is a zero of \(F\).

The 34-face geometric argument is checked from that box. Each of nine
active center triangles has an equal-distance witness by the defining
equations; five inactive center triangles have strictly closer rational
witnesses from the midpoint circumcenters. A triangle whose centers share
a point of distance at most \(r_*\) covers its convex hull: with barycentric
weights at \(x\), the weighted sum of squared distances to the centers is
the weighted sum at the witness minus the squared distance from the witness
to \(x\). For a boundary triangle with one anchor and two centers, the
anchor lies in both disks and the line segment connecting centers is covered
because their distance is at most \(2r_*\); convexity then covers the triangle.
A boundary triangle with two anchors and one center is covered immediately
by both anchor contacts and convexity.

The interval checker orients each actual triangle positively. Internal
edges cancel in the formal oriented boundary sum, leaving precisely the
positive convex decagon on the unit anchors. For a point off all triangle
edges the winding number of the chain's boundary is the sum of its
individual oriented triangle winding numbers. Inside the decagon it is
one, hence the point belongs to a triangle. Closure gives the entire
decagon. For each consecutive anchor pair the owner's direction lies in
their acute angular cone. The maximum squared distance to that center
along the short unit-circle arc is at an endpoint. Both endpoint contacts
are tight, so the corresponding circular cap is covered by convexity.
This certifies the whole closed disk; it does not require assuming global
nonoverlap of the triangular faces. At one anchor all remaining disks
are strictly farther than \(r_*\), proving this construction is tight
for its own centers, not that other arrangements cannot improve it.

The second command is a separate certificate using only the printed
18-decimal centers as exact rationals, with radius \(0.346645456927389645\).
It checks 237 interior triple intersections, 156 boundary intersections
of pair bisectors, 26 boundary stationary points, and one fixed boundary
reference. This bound is strictly below the branch test radius used above.
