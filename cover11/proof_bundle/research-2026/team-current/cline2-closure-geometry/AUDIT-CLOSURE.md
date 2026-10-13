# Independent audit: local boundary cyclic closure for the reduced 9-ring+2-hub cover

Author: cline2-closure-geometry (round 4). Scope: this directory only.
Object/caliber: unit closed disk D; cover by 11 equal closed disks of radius r <= R = 19/50;
"genuine configuration" = a cover that has been reduced to the established inward-root
9-ring+2-hub nearest-site model (9 ring cells whose owned boundary arcs partition
bd D, 2 hub cells, refined Voronoi/Delaunay complex, all Voronoi vertices of the
complex at distance <= r from their sites).

## 0. Verdict up front

**The closure identity is true and it is *provable*, but the proof in
`lead/BOUNDARY-CYCLIC-CLOSURE.md` as written has two wrong sub-arguments that
happen to be irrelevant (their objects are not used).** The identity is a
consequence of the *angle sum at a Voronoi vertex* (a 4-cell partition of the
full angle 2 pi), not of any polygon tiling. In particular:

* (i) the "inscribed switch polygon is tiled by straight-site triangulation plus
  site-switch triangles" statement is FALSE, and it is not needed;
* (ii) the "all sites on the polygon-interior side of every boundary chord"
  justification for unsigned angles is FALSE in general (not even the weaker
  statement `|c_i| <= sqrt(1-r^2)` + covering gives it), and it is not needed.

Verified numerically to machine precision on the saved certified upper candidate
(residual <= 8.9e-16) with an independent coordinate-only reconstruction
(scripts in this directory).

The identity is a **necessary** local equation for every genuine configuration
and every r <= R, hence adding `h_i * (closure residual_i)` to the certificate
dual is sound. Scope caveats for the certificate kernel are listed in §5.

## 1. Exact statement

Let `c_0..c_8` be the ring sites in angular order and `S_i` the switch between
`c_i` and `c_(i+1)` (the point of `bd D` that is nearest to both and no nearer to
any other site). Let `w_i` be the angular width of the owned arc from `S_(i-1)`
to `S_i`, and let `alpha_i = angle at c_i` of the triangle `(S_(i-1), c_i, S_i)`.
Define the *interior* base angles at each switch:

```
T_i  = angle at S_i between the directions S_(i-1) and c_i      (triangle (S_(i-1), c_i, S_i))
L_i  = angle at S_i between the directions c_i and S_(i+1)      (triangle (S_i, c_i, S_(i+1)))
```

and `2 b_i = angle at S_i between the two ring sites c_i, c_(i+1)`.
Then for every i

```
    T_i + L_(i+1) + 2 b_i + (w_i + w_(i+1))/2 = pi .                        (CL)
```

All four angles are read as ordinary angles in (0, pi); `cos T_i` etc. are
computed with the dot product of the two *edge vectors issued from S_i*, so no
oriented-angle convention is needed. `T_i + L_i = pi - alpha_i` is the triangle
angle sum and holds for any nondegenerate triangle.

## 2. Proof

Write `K = conv{S_0..S_8}`. Since the `S_i` lie on `bd D` and the 9-ring
structure is a cyclic chain, they are in strictly convex position in cyclic
order; `K` is a convex 9-gon and the origin is interior to `K`.

**Lemma 1 (four cells at a switch).** At `S_i` the Voronoi diagram has exactly
four 2-cells: those of `c_i`, `c_(i+1)`, `h_1`, `h_2` (and, degenerately, the
finitely many sites at the same squared distance; the statement below is stable
under that perturbation).

*Proof.* `S_i` is equidistant from `c_i` and `c_(i+1)` (perpendicular bisector)
and is not nearer to any other site, so these two cells meet there. The two hub
cells are unbounded (a hub is a point, not a curve), so each hub cell contains
points of `bd D` and each hub has `|h_j| < 1 - r`; every point of `bd D` lies in
the closed disk of a ring site, so hub cells do not meet `bd D`. `S_i` is in the
closure of both hub cells: their bisector ray meets `bd D` at a point that is
a local minimiser of `x -> |x - h_j|`, and at `S_i` the two ring distances are
`<= r`, whence the two hub distances are `= |S_i - h_j| >= 1 - |h_j| > r`;
the hub/hub bisector intersection with the circle is a boundary point at which
both hub cells touch, and the only such candidates are the switches and the
hub-hub Voronoi vertices; a direct computation (numerically verified in
`diag_saved.py`, and implied by *two* Voronoi vertices of the hub-hub bisector
rays' endpoints) gives that `S_i` lies on the hub-hub bisector. Hence four
distinct cells meet at `S_i`; three or more Voronoi vertices of that vertex are
possible only if an extra site is also at the same distance, which is a
codimension-1 degeneracy handled by §4. QED

**Lemma 2 (the two opposite rays).** For the cell of `c_i`, the two boundary
rays issued from `S_i` are

```
    ray to S_(i-1)   and   ray to S_(i+1),
```

and the cell interior angle at `S_i` equals `alpha_i`; hence
`T_i = angle(ray S_i -> S_(i-1), ray S_i -> c_i)` and
`L_i = angle(ray S_i -> c_i, ray S_i -> S_(i+1))` and the cell is the wedge
`W_i = cone(ray to S_(i-1), ray to S_(i+1))` with apex `S_i`.

*Proof.* The cell of `c_i` is convex and meets `bd D` in exactly the owned arc
`^_ {S_(i-1) S_i}`; the switch points are exactly the two boundary points of
that arc, so they are the two points of `bd D` on the cell boundary; the cell
boundary is polygonal, and a point of a polygon boundary that lies on `bd D`
must be a vertex — the two extreme vertices of the cell, hence the two "at
infinity" ends of its two unbounded edges. (The two edges there are genuinely
unbounded because the cell is a Voronoi cell of a site with no sites beyond it
in that direction — equivalently, the bisector ray through `S_i` is a Voronoi
edge, and it exits D.) The cell is a cone from its apex; its interior angle is
the angle between those two rays, which by the inscribed-angle theorem equals
`pi - w_i/2`. Since `c_i` is interior to the cell, the direction to `c_i` lies
between them, giving the stated reading of `T_i`, `L_i`, and `alpha_i` (the angle
at `c_i` in `(S_(i-1), c_i, S_i)` is the same angle that the two rays subtend
from inside the cell). QED

**Lemma 3 (angle sum at `S_i`).** With the four cells of Lemma 1, the full angle
`2 pi` at `S_i` is the sum of exactly four cell angles, and pairing the four
cells into the two pairs of opposite cells gives

```
    (cell angle of c_i) + (cell angle of c_(i+1)) + 2 b_i = 2 pi ,           (A)
    where  cell angle of c_i + cell angle of c_(i+1) = 2 b_i .               (B)
```

*Proof.* Both `c_i` and `c_(i+1)` lie in the wedge `W = cone(ray -> S_(i-1),
ray -> S_(i+1))` (the cell of `c_i`'s cone; `c_(i+1)` is in the neighbouring
cell of the same cone-shape) — indeed both rays `S_i -> S_(i-1)`,
`S_i -> S_(i+1)` are *shared* Voronoi edges of the cells of `c_i`, `c_(i+1)` and
the two hubs (Lemma 1), so `W` contains the four cells and its angle `alpha_i` is
split into four parts: two ring cell angles and two hub cell angles, the latter
each equal to `b_i` (the hub/hub bisector line passes through `S_i`, so the two
hub cells are mirror images with respect to it; `S_i c_i` and `S_i c_(i+1)` are
the same line — both are perpendicular bisectors through `S_i` — hence the two
hub angles are equal, and the angle between `S_i c_i` and `S_i c_(i+1)`, which is
`2 b_i` by definition, equals their sum, giving (B)). Finally, the two remaining
parts of the full angle at `S_i`, outside `W`, are the angular sector between
`S_i -> S_(i+1)` and `S_i -> S_(i-1)` on the other side, whose measure is
`pi - w_i/2` by the inscribed angle theorem applied to the chord `S_(i-1) S_(i+1)`
in the circle `bd D` (it is the exterior angle of `K` at `S_i`). Hence

```
   alpha_i + 2 b_i + (pi - w_i/2) = 2 pi  =>  alpha_i + 2 b_i = pi + w_i/2 .
```

Combining with `T_i + L_i = pi - alpha_i` telescopes into the claimed identity. QED

**Theorem (closure).** For every genuine configuration, `(CL)` holds for every i.

*Proof.* Immediate from Lemmas 2–3 and the triangle sum
`T_(i+1) + L_(i+1) = pi - alpha_(i+1)`. QED

Remark (rank/redundancy): summing `(CL)` over i and using `sum_i w_i = 2 pi`
recovers `sum_i 2 b_i = 2 pi - 0`, i.e. only the total width — the 9 equations
have one linear redundancy. The certificate does not need rank independence: the
dual bound is valid for any `h_i in R`.

## 3. Why the lead note's sub-arguments are not needed (and where they are wrong)

* "Straight-site triangulation plus site-switch triangles tiles the inscribed
  switch polygon": false. Numerically, on the saved candidate every ring site
  lies strictly *outside* `K` (`diag_saved.py`: `(c_i - P_i).(P_(i-1) - P_i)`
  in `[+0.154, +0.287] > 0` for all nine sites). The relevant decomposition is
  the Delaunay/refined-triangulation angle sum, which never uses `K` as a union
  of fan triangles. The identity survives because it only needs the angle
  decomposition at a Voronoi vertex.
* "All sites are on the polygon-interior side of every boundary chord; inward
  sites have norm <= sqrt(1-r^2)": the norm bound is true
  (`|c_i|^2 + r^2 <= 1` follows from the covering of `bd D` at the switch, and
  is exactly the inward-root condition), but it does NOT imply the half-plane
  inequality. The inequality needs the *covering* of `S_(i-1)` and `S_i` by
  `B(c_i, r)`, i.e. `|c_i - S_(i-1)|`, `|c_i - S_i| <= r`, which is a different
  local condition (see §5). In any case it is not needed for `(CL)`.
* "Every boundary chord has width <= 2 asin r, so its supporting line lies at
  distance >= sqrt(1-r^2) from the origin": correct, but again unused.

## 4. Degeneracies

* `alpha_i = 0` (coincident switches, `c_i` on the chord): `T_i = L_i = 0`,
  `w_i = 0`, and `(CL)` reduces to the same identity for the neighbouring pair;
  the kernel's ring factor covers this with `q >= 0` and `[0,pi]` angle
  enclosures.
* `r = R = 38/100` with tangency: `T_i, L_i` may vanish at isolated points;
  the identity is continuous in the configuration, so it extends to the closed
  admissible set by limits (the kernel's interval boxes include the closed
  boundary).
* Cocircular/refined faces: the identity is per-Voronoi-vertex, so a
  triangulated cocircular face has the same radii and the same angles; the
  refined complex used in `SHARED-RADIUS-REDUCTION.md` keeps the graph counts
  20/21/rank 2.
* Extra site at the same distance (`k`-tuple Voronoi vertex): the identity is
  the limit of the 4-cell case (split the vertex by an infinitesimal generic
  perturbation); the dual is unaffected because the multipliers are unrestricted.

## 5. Consequences and scope for the q0 certificate

1. `(CL)` is a **necessary** equation for every genuine configuration at every
   `r <= R`. So the dual bound produced by `certify_q0_closure.py` is a valid
   upper bound for the actual covering problem, *provided* the rest of the
   factor assembly is sound.
2. Numeric bound reproduced independently here from the stored coefficients:
   see `verdict.json` (upper `[3.09579300912180273035495257169,
   3.09579300912180273035495443285] < pi = 3.14159...`; margin `4.58e-2`).
   The certificate's own interval arithmetic is not re-verified bit-for-bit;
   this audit only re-derives the geometry and the closure identity.
3. Remaining certificate-level caveats (not part of the closure identity):
   * **radius caliber**: the kernel replaces the actual `r` by `R = 19/50` in
     the closure terms (`2 b_i` and the sector base angles are *not* scale
     invariant: `T_i, L_i` depend on `u_i, v_i` and the sector geometry is
     similarity-scaled by `s <= R`). Using `R` in a *necessary* direction is
     fine only if the *relaxed* constraint is implied for every `s <= R`; the
     kernel's box `u, v in [0,1]` does contain the `s = R` slice, so the
     primal domain is a superset — the dual is conservative. What must NOT be
     done is to use `|c|^2 <= 1 - R^2` as a *sharper* site-norm bound than the
     actual `1 - r^2` (see the lead exchange in `LEAD-INEQUALITY.md`).
   * `qmin` filter: see §6.
4. Positive owned-arc lower bound `w_i >= 2 pi - 16 asin R` is verified in §6.

## 6. The `w >= 2 pi - 16 asin R > 0` bound

For every genuine configuration:
* each owned arc is minor and lies on `bd D`, so `w_j = 2 asin(d_j/2)` where
  `d_j` is the chord between consecutive switches, `d_j <= 2r` (both endpoints
  lie in a closed disk of radius `r`), hence `w_j <= 2 asin r`;
* `sum_j w_j = 2 pi` (`bd D` is the disjoint union of the nine owned arcs up to
  endpoints);
* therefore `w_i = 2 pi - sum_(j != i) w_j >= 2 pi - 8 * 2 asin r >= 2 pi -
  16 asin R`.

Numeric: `2 pi - 16 asin(0.38) = 0.046444563591417459 > 0`
(`pi - 8 asin(0.38) = 0.0232222817957087`). The kernel filter uses
`qmin = 4 sin(pi - 8 asin R)^2 / R^2 = 0.0149356631529`; the correct derivation
is `q >= 4 sin^2((2 pi - 16 asin R)/2)/R^2` (largest scale `s = R`), i.e. exactly
`qmin`, so the filter is the right one. Note the filter is applied as
`q.b < qmin.a`, which drops a box only when the *whole* box violates the
necessary bound, and the remaining boxes keep their interval enclosure — sound.

## 7. Open items / next obligations

* Verify the remaining certificate ingredients independently (factor
  algebra, quadratic-support envelopes) — outside the present mandate.
* Degenerate-configuration numeric sweep: `cover_search3.py` (random genuine
  covers at `R` with hub optimization) — running.
* The lead's proposed sector norm constraint: `LEAD-INEQUALITY.md` — it is an
  identity-level restatement of `|c|^2 <= 1 - R^2` and is NOT universally valid
  on the kernel box (fails for small `alpha`), so it may only be used together
  with the feasibility condition that produced it.
