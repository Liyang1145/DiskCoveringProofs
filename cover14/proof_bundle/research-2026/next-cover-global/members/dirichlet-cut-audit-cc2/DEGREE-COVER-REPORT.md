# Analytic audit — DEGREE-COVER-WITHOUT-EMBEDDING.md (surjectivity-only cover certificate)

Auditor: dirichlet-cut-audit-cc2. Scope: one focused analytic pass on the strictly weaker theorem;
counterexample hunt at inverted/degenerate triangles, exterior sites, degree zero; the
given-coordinates vs. formal-β distinction; the optional repeated-anchor question. No claims, no review
events, no numeric runs; only this file written. The strict flat-disk audit is not repeated here; it is
cited only where the new theorem's scope is compared.

File audited: `lead/DEGREE-COVER-WITHOUT-EMBEDDING.md` (26 lines), plus the already-read
`lead/FLAT-DISK-REALIZATION.md` (amended), `lead/FLAT-DISK-ANGLE-INTERFACE.md`,
`lead/CYCLIC-POLYGON-CLOSURE.md` (C1251) for the boundary-order statements.

## 0. Verdict

**The topological core is correct and the weakening is real**: surjectivity onto the boundary polygon is
all that coverage needs, the proof is a valid winding/null-homotopy argument, and no counterexample
exists inside the stated hypotheses (checked separately for degenerate/inverted triangles and for sites
outside D). One wording risk is load-bearing and I give an **explicit counterexample** to the weakened
reading of the boundary hypothesis (§2): if "boundary vertices in their combinatorial order map to a
simple convex polygon P" is read as "the boundary vertex *set* is the vertex set of a convex polygon",
the theorem is **false** (degree-0 boundary loop, all triangle images covered, the polygon centre
uncovered). The file's own §6 last sentence states the correct general hypothesis ("any boundary loop of
nonzero winding throughout the target region"); the earlier sentence should be aligned with it.

For Cartesian certificates the claim "this removes all orientation and interior general-position
obligations" is **true for the interior and false for the boundary**: triangle positivity/nondegeneracy,
orientation (det signs), interior flatness/angle-ledger and injectivity are all removed; what remains is
(a) the boundary loop's order/winding condition (an orientation condition, but only on the boundary and
finitely checkable), (b) the finite metric conditions per real triangle (existence of a common witness
with all three distances ≤ U, i.e. minimal-enclosing-circle radius ≤ U), (c) incidence distances
|v − A_e| ≤ U, (d) U < 1 (in fact U ≤ 1 suffices for the cap step), and (e) the combinatorial fact that
K is a triangulated disk. And the new theorem does **not** manufacture coordinates from angle data (§6).

## 1. The topological core — proof verified, with the exact hypotheses

Statement (reconstructed precisely): K a finite combinatorial triangulated compact disk; vertex images
p_v ∈ R² with repetitions allowed; F affine on each triangle, hence well defined and continuous
(adjacent affine maps agree on the shared edge because they agree at its two endpoints). Let
γ = F|∂K be the boundary loop. Suppose:
(T1) γ has nonzero winding about every point of the target region (in the file's phrasing: the boundary
vertices in combinatorial order trace a simple convex polygon P, i.e. the polygon is traversed exactly
once in its cyclic order);
(T2) there is one *common* finite site set {c_i} with F(t) ⊆ ∪_i B(c_i,U) for every triangle t.
Then P ⊆ ∪_i B(c_i,U).
Proof, re-derived: if x ∈ int P were outside F(|K|), then F is a continuous map (|K|,∂|K|) → (R²∖{x}, ·);
|K| is contractible, so γ is null-homotopic in R²∖{x}, forcing wind(γ,x) = 0, contradicting (T1).
Hence int P ⊆ F(|K|); F(|K|) is compact hence closed, so P = closure(int P) ⊆ F(|K|). Every point of
F(|K|) lies in the (closed) image of at least one triangle, and each such image is covered by (T2).
∎
Checks: no positivity, no local injectivity, no equality of radii, no interior flatness is used anywhere;
the only uses of continuity are the null-homotopy and the agreement on shared edges; the degree of F is
±1 (so the number of preimages of a generic interior point is odd, in particular ≥ 1) — "inverted faces
may cancel in the degree sum but cannot remove every preimage" is exactly right. (T2) must be stated with
*one common* site set for all triangles; with a per-triangle site set the conclusion does not follow.
The theorem's entire content is the inclusion P ⊆ F(|K|): (T2) already gives F(|K|) ⊆ ∪_i B(c_i,U).
This is the clean sense in which it is strictly weaker than C1254: C1254 concludes an embedding
(injectivity + flatness), this concludes only surjectivity of the PL map, and its metric hypothesis
(common witness, arbitrary distances ≤ U) is weaker than C1257's equal-circumradius hypothesis.

## 2. Explicit counterexample to the weakened boundary reading (degree zero)

Take the square P = [0,1]² with corners a=(0,0), b=(1,0), c=(1,1), d=(0,1). Let K be a 6-gon disk with
boundary vertices v_1..v_6 (cyclic) and images
  v_1..v_6 ↦ a, b, c, d, c, b   (closing edge v_6→v_1 maps to the segment [b,a]).
So γ is the three-side path a→b→c→d followed by its reverse d→c→b→a (the square's fourth side d–a is
never traversed, and no side is traversed twice in the same direction):
  image(γ) = [a,b] ∪ [b,c] ∪ [c,d],   wind(γ, x) = 0 for every x ∈ int P.
The *set* of boundary vertex images is exactly the vertex set of the simple convex polygon P.
Triangulate K by ear-clipping: triangles {v_1,v_2,v_6}, {v_2,v_3,v_6}, {v_3,v_5,v_6}, {v_3,v_4,v_5}.
Their images are respectively the segments
  (a,b,b) = [a,b], (b,c,b) = [b,c], (c,c,b) = [b,c], (c,d,c) = [c,d],
so F(|K|) = [a,b] ∪ [b,c] ∪ [c,d] (the three traversed sides only). Take the **four corner sites**
a,b,c,d and U = 1/2 (closed disks), i.e. coverage by the *union* of the site disks: for t ∈ [0,1], the
segment point (t,0) has distances t and 1−t to a and b, so min ≤ 1/2; likewise (1,s) has min ≤ 1/2 from
{b,c} and (t,1) has min ≤ 1/2 from {c,d}. Hence every triangle image is covered by the union of the four
disks (the midpoints (1/2,0), (1,1/2) lie at distance exactly 1/2, so the closed disks are needed), and
(T2) with the common site set {a,b,c,d} holds. (Note: [a,b] is *not* contained in B(a,1/2) alone — b is at
distance 1 from a; only the union covers it, and replacing the corner sites by segment midpoints would
cover the centre and destroy the example.)
But int P ⊄ F(|K|): the point (1/2,1/2) is at distance √2/2 ≈ 0.7071 > 1/2 from all four sites and is
**not covered**. Conclusion fails.
What this shows: the hypothesis is essential in its winding form; "the boundary vertex set is the vertex
set of a convex polygon" is not enough, and neither is "the boundary path runs along an arc of P once"
(the counterexample's loop runs along three sides and then unwinds). Consequences for the file: state the
hypothesis as (T1), i.e. γ has winding ±1 about every point of the target region (equivalently: the
boundary polygon is simple convex *and traversed once in cyclic order*); the file's §6 last sentence
already says this. Also note (T1) is about nonzero winding only, so a *non-simple* boundary with winding 2
(e.g. five anchors on S¹ with each angular step 0.8π < π, total 4π) still gives surjectivity of the star's
interior — but then the target region is the star, not the convex hull, and the application's cap
accounting (§5, §7) must be redone. This is the precise sense in which "one winding" (not merely
"gaps < π") is the application-level requirement.

## 3. Counterexample hunt 1: inverted / degenerate / crossing triangles — none

The real-triangle step is orientation- and shape-blind by construction. For vertex images u,v,w and
x = Σλ_i v_i (λ_i ≥ 0, Σλ_i = 1) with any common witness O:
  Σλ_i |x − v_i|² = Σλ_i |v_i − O|² − |x − O|²  ≤  U²      (exact; verified by expanding with O at the
origin and using x = Σλ_i v_i to cancel the cross term). Hence min_i |x − v_i| ≤ U. The identity involves
only the positions of u,v,w and O: it does not see the sign of any determinant, whether the triangle is
acute/obtuse/inverted, or whether its image lies inside any other piece. Degenerate cases are covered by
the same inequality: an affine image of a combinatorial triangle is the convex hull of the three vertex
images, so if u,v,w are collinear the image is a segment whose every point still has barycentric weights
λ ≥ 0; repeated vertices give a sub-segment or a point. Thus condition 1 of §10 of the file is exactly
"the minimal enclosing circle of {u,v,w} has radius ≤ U" — orientation-free, and *strictly weaker* than
"circumradius ≤ U" (for an obtuse triple the MEC is the longest-side half-diameter). A triangle can only
fail the new hypotheses by having an *uncovered* image, which is excluded by (T2)/condition 1 itself —
so there is no counterexample of the requested type at inverted/degenerate triangles. Crossing/overlapping
images are likewise irrelevant to the conclusion (they can only enlarge F(|K|)).

## 4. Counterexample hunt 2: exterior sites — none

The cap step is the only place where a site's position relative to D could matter, and it does not need
v ∈ D. Re-derived: let the two arc endpoints be in B(v,U) with U ≤ 1 and separated by the minor arc of
length θ < π. If that arc contained the circle point farthest from v (direction opposite v; if v = 0 the
whole circle is at distance 1 > U, so no endpoints exist), write the endpoints at angular offsets π−a and
π+b from arg v with a,b > 0, a+b = θ < π. Then |endpoint − v|² = 1 + |v|² + 2|v| cos a ≤ U² ≤ 1 forces
cos a ≤ −|v|/2 < 0, so a > π/2; symmetrically b > π/2; hence θ = a+b > π, contradiction. So the arc avoids
the far point and the distance |w − v| is maximized at an arc endpoint, hence ≤ U throughout; the cap is
conv(arc) and convexity finishes. Equivalently (the file's route): for v ≠ 0, B(v,U) ∩ S¹ is
{cos(t − arg v) ≥ (1+|v|²−U²)/(2|v|)} with the right-hand side > 0, a single arc of width < π containing
both endpoints, hence containing the minor arc between them. No hypothesis |v| ≤ 1 is used, matching the
file's "This does not require v inside D". The virtual and owner steps use only pairwise incidence
distances, not site location, so exterior sites create no failure either.

## 5. The augmented-graph application, condition by condition

K+ combinatorics: the same 24 vertices, 36 triangles as in C1257 (V−E+F = 24−59+36 = 1); only the
metric/angle assumptions are dropped, coordinates are now data.
- Condition 1 (real triangle: ∃ witness O_f with all three site distances ≤ U). Verified above; implies
  F(t) ⊆ B(u,U) ∪ B(v,U) ∪ B(w,U), i.e. the image is covered by the site disks at its vertices.
- Condition 2 (every site-anchor incidence |v − A_e| ≤ U). Used twice: (i) virtual triangle, with
  M = (u+v)/2 the image midpoint: |M − u| = |u−v|/2 ≤ (|u−A_e| + |A_e−v|)/2 ≤ U, and the distance to u (and
  to v) is maximized at a vertex of each half-image triangle (A_e,u,M), (A_e,v,M), so the two halves are
  covered by B(u,U) and B(v,U); (ii) owner triangle, all three image vertices within U of its site, so
  convexity gives the whole image ⊆ B(v,U). Both arguments are orientation-free and survive degenerate
  (collinear/coincident) vertices.
- Condition 3 (0 < U < 1, each owner assigned to the minor arc between its adjacent anchors) plus
  condition 2 gives the caps by §4, hence D = P ∪ (union of caps) ⊆ ∪_{sites} B(site,U).
Every covering disk is centred at a **site**; anchors occur only as boundary vertices, never as disk
centres, and the number of disks is the number of sites — so the output is exactly a 14-disk cover of D
at radius U in the q10,m4 instance. Conclusion of §4–§5 agrees with the file.

## 6. Given global coordinates vs. formal β assignments (type-checking)

- C1257's input: angle/radius data (β_e, R_f, a_e) satisfying the listed equations (face γ-sums,
  hidden-site Σβ = 2π, α_v ∈ (0,π), γ_A ∈ (0,π/2), L_v < 2, Σθ = 2π, and the *imposed* per-anchor C1252
  closure). Output: existence of compatible coordinates plus a cover.
- This file's input: explicit coordinates of all 24 vertices (or a PL map), plus the boundary condition,
  plus per-triangle image coverage (T2)/conditions 1–3. Output: P ⊆ ∪_i B(c_i,U), and for the inscribed
  anchor polygon, a cover of D.
So the two are not substitutes: the new theorem presupposes the coordinates that C1257 constructs from
angles. Its value is different and real: *if* a certificate carries Cartesian coordinates as variables
(e.g. a polynomial system whose solution box is certified), then coverage can be concluded from the
listed finite, orientation-free conditions, without proving triangle positivity, orientation, interior
flatness, or the angle ledger. Conversely the new theorem gives no route from angle data to covers and no
existence statement for coordinates. Consistency check: C1257/C1254 real triangles have equal circumradius
R_f ≤ U, which is a special case of condition 1 (the circumcentre is a witness) — so the new hypotheses
are implied by the old ones, confirming the weakening is genuine and not an unrelated statement.
Scope note the file makes correctly and that should stay: nothing here declares arbitrary degenerate
angle assignments realizable, and no global lower bound follows.

## 7. Optional question: repeated anchors with weakly ordered circle angles

**Yes, allowed, with a precise proviso.** Suppose the anchor images lie on S¹, with the angular
increments along the *combinatorial* order satisfying
  (a) every increment ∈ [0,π)  (nonnegative *and* strictly less than π — this must be required, not just
      nonnegativity),
  (b) the increments sum to 2π (exactly one winding),
  (c) each *positive* increment's two endpoints are incident to a common site (automatic for consecutive
      boundary edges, which share their boundary site).
Then:
(i) cumulating the increments gives a strictly increasing angular function from θ_1 to θ_1+2π (ties
exactly at the zero increments), so the anchor points appear in cyclic angular order and the collapsed
polygon — contract consecutive zero edges, i.e. keep the distinct anchors — is a convex polygon traversed
once, with degenerate spike edges; spikes do not change the winding, so wind = 1 on its interior and (T1)
holds for P = that polygon;
(ii) D ∖ P = disjoint union of the caps of the *positive* increments (each such cap is the minor segment
bounded by a chord and the arc of length < π, by (a)), and zero increments contribute no 2-dimensional
region;
(iii) each positive-increment cap is covered by its common incident site's disk by §4, since both of its
anchor endpoints are within U of that site;
(iv) owner triangles with coincident anchors degenerate to segments and are covered by convexity;
(v) repeated *points* are harmless and need no separate exclusion: an anchor can occur at several
positions only within (or at the ends of) zero-increment runs, i.e. at the same angular position, and a
"return to an earlier point" after a nonempty sub-path would require that sub-path to sum to a multiple of
2π, which by (a)+(b) happens only for the full lap, where it is the closing of the same point. The
convex-polygon conclusion of (i) is therefore stated after contraction, not as an exclusion of repeats.
Why (a) is needed and not just monotonicity: the cap of a positive increment is the region bounded by the
chord and the arc *in the traversal direction*; the single-arc lemma of §4 applies to arcs of length < π.
For an increment ≥ π that arc is not the minor one, the lemma does not apply, and with U < 1 the case
cannot be saved by the owner's disk anyway (two points at angular separation ≥ π are at distance ≥ √2 > ...
for separation exactly π they are antipodal, distance 2, and no point is within U < 1 of both).
Failure modes to state: (a') if only "each increment < π" is verified and the total is 2π·k with k ≥ 2
(star example, five anchors with 0.8π steps, total 4π), the loop's interior is not the convex hull, the
caps no longer tile D ∖ P, and the application-level conclusion must be re-derived (though the bare
surjectivity of §1 still holds for the star's own interior); (b') if the increments are not monotone (any
negative step), the combinatorial neighbours of a cap are not the two anchors of one site, the
cap-to-owner assignment breaks, and the coverage argument fails even though the winding may still be
nonzero. So for the application, winding 1 alone is *not* sufficient: the weak angular order with the
bound [0,π) is what supplies both D = P ⊔ caps and the cap-to-owner assignment.

## 8. Obligations / precision list

**P1 (essential, with counterexample).** Restate the boundary hypothesis as (T1): the boundary loop has
nonzero winding about every point of the target region; in the convex-polygon formulation add "traversed
exactly once in its cyclic order". Without this, §2's construction (all images covered, centre uncovered)
falsifies the conclusion. The file's §6 last sentence is already the correct form; the first sentence
should be aligned with it, and the pentagram example shows why "gaps < π" is not a substitute for
"one winding" at the application level (§7).
**P2.** Say explicitly that the site set is common to all triangles (per-triangle sets break the
conclusion).
**P3.** In the cap step: state U ≤ 1 (the file's 0 < U < 1 is fine), note v ≠ 0 is needed only to write
the intersection as a single arc (at v = 0 with U ≤ 1 the disk either covers D or misses S¹ entirely), and
record that the cap's two anchor endpoints are incident to the *same* site — that incidence, not the arc
geometry, is what assigns each cap to a disk.
**P4.** Condition 1 = "∃ common witness" should be identified as "minimal enclosing circle radius ≤ U"
(finite, orientation-free, strictly weaker than circumradius ≤ U; for obtuse triples it is
longest-side/2 ≤ U). This is the condition a Cartesian certificate must verify per real triangle.
**P5.** The "removes all orientation obligations" phrasing should be narrowed to "removes all *interior*
orientation/general-position obligations": the boundary order/winding condition (P1) and the incidence
inequalities remain, i.e. obligations (a)–(e) listed in §0.
**P6.** The compact-limit remark in §24 is consistent provided the limiting boundary condition is taken
as the closed form "weakly ordered increments, total 2π, one winding" and the per-triangle witness
condition is closed in the coordinates (it is: {∃O : all |O−v_i| ≤ U} ⟺ MEC ≤ U is closed, and image
coverage of compact triangle images by closed disks is closed). I did not audit the necessity inputs
C1171/C1172 that the remark cites.

## 9. What this establishes and what it does not

Establishes (conditional): with coordinates given, the boundary loop winding once around the target and
the finite conditions 1–3 are enough for P ⊆ ∪_i B(c_i,U), hence for a cover of D in the inscribed-anchor
application — with no triangle positivity, orientation, injectivity, interior flatness or angle-ledger
input. Does not establish: existence of coordinates from angle data (that remains C1254/C1257's job), any
statement about degenerate angle assignments, the necessity direction, or any global lower bound
(explicitly disclaimed in the file). Counterexample status: none inside the stated hypotheses
(degenerate/inverted triangles, exterior sites all checked); exactly one counterexample outside them,
under the weakened boundary reading, given in §2; plus the star/winding-2 and non-monotone-order failure
modes of §7 at the application level.

## 10. Next minimal obligation (one)

Align the statement with P1 (§8) and add P2/P4/P5 as the explicit hypothesis list for the Cartesian
application. Nothing else is needed for the weaker interface: with P1 the winding argument is complete,
and §3–§5 already supply the three coverage sub-arguments and the cap lemma in an orientation-free form.
