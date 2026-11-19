<!-- SPDX-License-Identifier: MIT -->
# Ten disks: published theorem, direct construction, and replay obligations

**Status:** the optimum is proved in the cited primary literature. This note
independently proves the upper bound but does **not** reproduce the lower-bound
proof in full and is not a fresh verification of it.

Gábor Fejes Tóth, [*Thinnest Covering of a Circle by Eight, Nine, or Ten
Congruent Circles*](https://library.slmath.org/books/Book52/files/18fejes.pdf),
*Combinatorial and Computational Geometry*, MSRI Publications 52 (2005),
pp. 361–376, states the theorem in §1, proves the common geometric reduction
and area argument in §2, and gives the remaining ten-disk argument in §3.
The cited paper uses unit covering disks and a variable target radius. Scaling
back to this repository's unit target gives
[
r_D(10)=rac{1}{1+2cos(2pi/9)}.
]

## Direct exact upper bound

Let (d=pi/9), (c=cos d), (r=(4c^2-1)^{-1}), and
(a=2rc). Place one center at the origin and the other nine at distance
(a) on the rays of angles (2kpi/9). The origin disk covers all points
at distance at most (r). For any other point, take its nearest ray,
let (sin[r,1]) be its distance from the origin and
(|	heta|le d) its angular distance from the ray. Its squared distance
to the associated center is at most (s^2-2sac+a^2). At (s=r) this
expression is (r^2), since (a=2rc); at (s=1) it is also (r^2), since
(1-4rc^2+4r^2c^2-r^2=(1-r)(1-r(4c^2-1))=0).
Convexity in (s) gives the required bound on the entire interval.

## Lower-bound proof map and limits of this check

At the proposed target radius (R=1/r), seven unit disks cannot cover
the circumference by angular capacity, but eight are not excluded by
capacity alone. A disk covering the origin cannot meet the target
circumference since (R>2). The extra work compared to the eight- and
nine-disk proofs is therefore substantial:

1. **Exclude an eight-disk boundary cover.** In the eight-owner arrangement
   of §3, let (p_i) denote the inward meeting point of each consecutive
   pair. The remaining two disks must together contain all eight such
   points. The proposition on pp. 368–371 proves
   (|p_i-p_{i+3}|>2) and (|p_i-p_{i+4}|>2) modulo eight. The first
   prohibition requires the two disks to alternate colors along the
   cycle with step three, giving ordinary index parity as the colors.
   The second prohibits a pair of the same parity from sharing a disk.
   The radial estimate (h(artheta)) for the inner meeting point
   and the angular intervals for the relevant pairs still need
   separate reconstruction to replay this argument here.
2. **Exclude outer triple junctions in the nine-owner case.** Section 3
   reduces these junctions to one outer triple or two with one common
   owner. The two diagrams in Figure 3 encode the region partitions.
   The resulting area estimates (9)–(13) and their primed version give
   contradictions. To reproduce them, derive the partitions without
   assuming the pictured configuration, check the area inequalities
   and all branch conditions, and bound the elementary functions by
   directed intervals. The first branch's printed final bounds are
   separated by only about (4	imes10^{-5}) in the paper's units;
   passing an ordinary floating-point check would not certify that gap.
3. The remaining one-interior/nine-boundary pattern is fed back into
   the shared argument of §2. A fresh end-to-end proof must include that
   step, including its equality or strictness argument, not merely
   rule out the other configurations.

There is an apparent reversed inequality on p. 370 immediately before
the convexity argument for (h). For the two selected disjoint pairs,
write their pair arc measures as (artheta_1,artheta_j). The four
other disks each contribute angular measure at most (2arcsin(1/R)).
Subadditivity of angular length and full boundary coverage therefore
give (artheta_1+artheta_jge 2pi-8arcsin(1/R)), rather than the
printed direction. This is the direction needed to apply Jensen followed
by monotonically increasing (h); it does not by itself replay the
radial or angular lemmas.

Treat this order as **literature-proved, native upper bound verified
analytically, native lower-bound replay incomplete**.
