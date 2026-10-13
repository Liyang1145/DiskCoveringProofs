# GRAPH-INTERFACE-CHECK — the combinatorial coverage of the q0/q1 classification, with paragraph pointers

**Auditor**: r20-gluing lane (cline2-r23-gluing). Read-only; **no claim registered**. Read for this
note: `flash-structure/GLOBAL-TOPOLOGICAL-REDUCTION.md`, `lead/VORONOI-BOUNDARY-REDUCTION.md`,
`flash-structure/REVIEW-VORONOI-BOUNDARY-REDUCTION.md`, `flash-structure/AUDIT-HUB-EDGE-BRIDGE-AND-Q-CLASSES.md`,
`lead/INWARD-ARC-SWITCH-UNIQUENESS.md`, `lead/R20-CHAIN-HUB-CONVEXIFICATION.md` (C879), claims
C809/C817/C818/C819/C824. Own computations: `graph_interface_check.py` / `.json`.

## 0. The proposition being checked (as stated by the lead)

*canonical inward 9 essential boundary arcs + 2 strict hubs, full cover ⇒ there exists a triangulation
with boundary vertices = arc order, 11 interior facets each noncollinear with `Rc ≤ r`, and the q0/q1
enumeration covers it.*

Verdict up front: the **existence / arc-order / interior-vertex / facet-`Rc ≤ r`** parts are properly
proved in the bearing files (pointers below; the facet clause is correct precisely because a primal
vertex is *equidistant* to its incident sites — my earlier objection to it was out of domain and is
withdrawn in §1.4); the enumeration is **conditional on the graph interface (P1)–(P3)**, one of whose
legs (the hub-edge bridge) is conditional on C450; and the one leg that is *not* free anywhere is the
**straight-site embedding (E-ext)** in §2′ — non-crossing is inherited from Delaunay, but that the
retained faces tile the arc-order polygon with no extra exterior triangle mixed in is an obligation.
My earlier blanket phrase "the four topology claims have no degeneracy leak" is refined in §3.

## 1. Clause-by-clause pointers in the bearing files

1. **Canonical inward, nine essential ordered boundary arcs.**
   * `flash-structure/GLOBAL-TOPOLOGICAL-REDUCTION.md` §0 (P1): nine boundary disks with essential,
     cyclically ordered arcs; only neighbouring arcs overlap; multiplicity ≤ 2; the two other disks
     strictly interior (`|h| + r < 1`); the eleven disks cover `D`.
   * `lead/VORONOI-BOUNDARY-REDUCTION.md` §1: every boundary disk owns **exactly one** connected
     nearest-centre boundary arc, of positive length — proof uses only: arcs proper and < π, overlap
     endpoints with opposite strict signs, one affine-line/circle intersection (transversality), and
     the hub side `|h| + r < 1 ⇒ |u−h| > r`. ⇒ the nine arcs' cyclic order and exactly nine distinct
     switches.
   * §3 there: inward-root replacement (C464) gives `|c_i| ≤ √(1−r²) < 1` and preserves coverage and
     the actual arcs; all eleven cells have nonempty interiors; the nine switch points have graph
     degree exactly 3 (secant bisector: distance from the origin `||c_i|²−|c_j|²|/(2|c_i−c_j|) ≤ (|c_i|+|c_j|)/2
     ≤ √(1−r²) < 1`). `REVIEW-VORONOI-BOUNDARY-REDUCTION.md` **R2** records that this degree-3 step is
     load-bearing (without it the count only gives `v ≤ 20`) and supplies the repaired two-line proof,
     including the touching-arc case (`ρ_i = r ⟺ o_i = 0`) and the "third boundary disk would be a
     triple overlap" exclusion.
2. **Boundary vertices = arc order; dual is a disk cellulation; hubs interior.**
   * `GLOBAL-TOPOLOGICAL-REDUCTION.md` §1(1.1)–(1.2): cells `V(c) ∩ D` are closed convex, interiors
     disjoint and covering `D`; each ring cell meets `∂D` in a nondegenerate arc; **each hub cell is
     inside `int D`** and contains its centre; the dual is a regular cell complex on a disk, its
     **boundary cycle has length 9 with edges exactly the nine distance-1 ring-ring adjacencies**; the
     two hub vertices are interior. **Two separate inclusions, not a chain** (my earlier
     "hub cell ⊆ int D ⊆ B(h,r)" was wrong, since `int D ⊄ B(h,r)`): the hub cell lies in `int D`
     (VORONOI §2: convexity + no boundary point is nearest to `h`), **and** independently the hub cell
     lies in `B(h,r)` (a covering disk at `x` in the hub cell gives `|x−h| ≤ |x−c| ≤ r`). Both are
     proved there; the consequence used is `h ∈ int D` and `|h| + r < 1`.
   * Same §2 remark (and §1(1.2)) explicitly warns that the inference "original ring adjacency ⇒
     active Voronoi adjacency" is **unsafe** and is bypassed — i.e. the arc-adjacency ↔ dual-boundary
     identification is derived, not assumed.
   * **Delaunay vs arc adjacency**: the dual constructed in §1(1.2) *is* the Delaunay graph of the
     eleven centres clipped to `D`, so the two agree by construction; the boundary of the Delaunay
     graph is the 9 ring vertices in arc order (VORONOI §1 + §1(1.2)). No separate assumption.
   * **Hub in the convex hull**: what is *used* everywhere is "hub cells ⊆ `int D`", hence hub vertices
     interior to the dual disk — proved (VORONOI §2, GLOBAL §1(1.2)). I found **no step in the
     classification chain that needs "hub ∈ conv(ring centres)"**; if a later step wants it, it is a
     new obligation, not an inherited one.
3. **Existence of the triangulation and the degenerate/cocircular handling.**
   * `GLOBAL-TOPOLOGICAL-REDUCTION.md` §1(3): a `k`-fold interior vertex has all incident cells
     containing it; refine each face of degree > 3 by *any* triangulation of its own vertices; the
     refinements are interior to disjoint faces and glue to a global refinement; **R3 (locality)
     is preserved**; the doc explicitly corrects the earlier false claim that a refinement cannot
     create ring-only faces (control: the quadrilateral `(h,i,i+1,i+2)` with diagonal `(i,i+2)`), and
     records the caveats: (iii) `q`, `K`, degrees are **refinement-dependent**; (iv) added diagonals
     must **not** be fed into strict positive edge/degree estimates; the remark gives a hub-fan
     refinement that avoids new ring-only faces.
   * `lead/VORONOI-BOUNDARY-REDUCTION.md` §3: high-order **cocircular** coincidences *decrease* the
     counts (`k`-fold vertex replaces `k−1` trivalent vertices joined by zero-length edges); zero-length
     edges are not counted.
   * `AUDIT-HUB-EDGE-BRIDGE-AND-Q-CLASSES.md` Part 2: rules R1–R5 (R3 locality *proved* for degenerate
     faces too; R5 ring-only faces = consecutive triples), and its "explicitly not proved here" list
     (realizability of q ≥ 1; exclusion of q ≥ 1 by counts alone; trivalence assumed by the count
     formulas and recovered by refinement).
4. **Facet condition `noncollinear Rc ≤ r` — WITHDRAWN objection; the clause is correct in domain.**
   My earlier "counterexample" (three unit disks with centres `(−0.9,0)`, `(0.9,0)`, `(0,0.1)` sharing
   `(0,0)` while the triangle's circumradius is `4.1 > 1`) is **out of the proposition's domain**: it is
   an arbitrary common covered point, not a primal (Voronoi) vertex. A true primal vertex `x` is
   **equidistant to all its incident sites**, so its empty circle has radius `r_x ≤ r`; three distinct
   sites on a circle of finite positive radius are non-collinear, and their circumradius is exactly
   `r_x ≤ r`. Refinement of a cocircular face stays on the same circle, so the bound survives
   refinement. This is the bearing interface as written in `lead/COMPATIBLE-EDGE-SUPPORT.md` §3 ¶34
   ("A true primal vertex is the center of an empty circle through its incident sites. Those sites, in
   cyclic order, form a convex cyclic polygon … A three-site collinearity cannot occur on a finite
   positive-radius circle with distinct sites. … zero-length primal diagonals mean cocircularity, not
   collinear sites."). **NOT MEC-only**: the MEC/obtuse substitution is what C900's control needs for
   *arbitrary* equal-radius disk triples, which is a different question; for the Voronoi-vertex facets
   the `Rc ≤ r` form is the correct one.
5. **Enumeration coverage.** `GLOBAL-TOPOLOGICAL-REDUCTION.md` §2 (chords cut empty ears; 8-gon
   obstruction), §2b (two-triple ⟹ `q ≤ 2`), §2c (five-ring star ⟹ `q ≤ 2` excluded, `q ≤ 1`),
   §3 (core, link proof, two-fan classification); metric facts in C809 (union-measure statements);
   class exclusions in C817 (q1 (5,7)), C818 (all q1), C819 (q0 (4,9)), C824 (q0 (5,8)) — all are
   **area/moment upper bounds over closed domains including zero limits**, so degeneracies cannot leak
   out of *these*; but the **class list itself** (q0/q1 and the hub-degree pairs) comes from the
   combinatorial interface (P1)–(P3), with **(P3) the hub-edge bridge conditional on the C450
   capacity certificate** (`AUDIT-HUB-EDGE-BRIDGE-AND-Q-CLASSES.md` Part 1 verdict: sound
   conditional on (H1) the branch hypothesis and (H2) the capacity certificate).

## 2. Independent verifications (`graph_interface_check.py`, `straight_site_control.py`)

1. **Withdrawn objection (see §1.4)**: the `Rc ≤ r` clause is correct in the Voronoi-vertex domain; my
   former "counterexample" is out of domain (arbitrary common point, sites not equidistant).
2. **8-gon lemma (A).** My own enumeration gives **132** triangulations of the 8-gon with vertex labels
   `0,2,3,…,8`, and **0** of them with all faces consecutive in `C_9` — reproducing the cited
   `Catalan(6)` exhaustive check.
3. **Ear counting (B).** My own enumeration of edge-disjoint ear sets on the 9-cycle (= independent
   sets of `C_9`) gives sizes `1, 9, 27, 30, 9`, and **none of size 5** — reproducing `AUDIT…` Part 2
   result (B) `q ≤ 4`.
4. **Straight-site embedding control on the saved configuration** (`straight_site_control.py`; floats,
   one configuration — a control, not a proof for the class):
   * the nine boundary arcs' cyclic order equals the ring sites' **angular** cyclic order (arc order
     `1,2,…,8,0` = angular order rotated);
   * the **radial-wedge property** holds: each ring site's own angle lies inside its own owned arc
     (9/9);
   * the polygon `P` through the ring sites **in arc order** is **simple**, contains **both hubs
     strictly inside**, and contains the origin;
   * the empty-circle (Delaunay) triangles of the eleven sites are **11**, **all** with circumcentre
     inside `D`, and their total area equals `area(P)` to `1e-12`: **no extra exterior triangle** is
     mixed in (the clipped dual *is* the full Delaunay triangulation here);
   * hub face-degrees `(7,6)` and `E = 21` — i.e. the saved configuration independently lands in the
     surviving `q0` class with hub degrees `(6,7)`, matching C819's control note.

## 2′. The straight-site embedding obligation (why the straight triangulation is legal)

What is already granted: the faces of the clipped dual are exactly the Delaunay triangles whose
circumcentre lies in `D` (definitional: dual face ↔ interior primal vertex), each such face is
non-degenerate with `Rc ≤ r` and lies inside the convex `D` (its vertices are sites in `D`), and its
straight edges are Delaunay edges, hence **pairwise non-crossing** (classical; this is the lead's
"Delaunay dual ⊆ full complex gives non-crossing"). **UPDATE — (E-ext) is discharged on the topological route** (`STRAIGHT-SITE-EMBEDDING-PROOF.md`,
written after the lead's correction): the refined dual `K` is a simplicial closed disk whose faces are
empty-circle polygons; fixing one triangulation of every cocircular class makes every simplex of `K` a
sub-simplex of a single planar Delaunay triangulation `𝒟`, whence `f(σ) ∩ f(τ) = f(σ ∩ τ)`, `f` is
injective, and (compact → Hausdorff) an embedding; Jordan–Schoenflies then gives that the image is
**exactly** the closed region bounded by the arc-order 9-cycle, so hubs strictly inside, no holes, no
missing faces and no extra exterior triangle follow automatically — without radial-wedge, without
`P = conv(sites)`, and without any "all circumcentres in `D`" hypothesis. The control recorded below is
kept as an illustration only.

**Why the angle accounting is then legitimate** (the reason (E-ext) mattered): the area duals use
"at each hub the full star winds once" and `alpha_i + Σ_f A_fi − b_left − b_right = π`, which need the
straight images of the incident triangles to genuinely surround the hub site and to meet the boundary
region — exactly what "`f(int |K|) = int f(|K|)`" and "the faces tile the Jordan region" supply.
Historic note (superseded): I had sketched radial-wedge and "all circumcentres in `D`" as sufficient
ingredients; neither is needed, and neither is assumed now.

## 3. Correction to my earlier statement ("the four topology claims have no degeneracy leak")

That blanket phrase is withdrawn and replaced by the precise form:
* **metric exclusions** (C809's star/two-triple lemmas; the area/moment duals of C817/C818/C819/C824):
  no degeneracy leak — they are relaxations over closed domains whose limits (tangency, zero radii)
  are explicitly included, and the relaxation direction is the right one for an upper bound;
* **the class enumeration** (which graphs exist, hub degrees, q values): depends on the combinatorial
  interface (P1)–(P3), and for non-trivalent/cocircular configurations it is covered only through the
  **refinement** device, whose own caveats must be carried (refinement-dependent `q/K/degrees`;
  added diagonals excluded from strict estimates). Within that interface it is sound; it is not
  "degeneracy-free by construction".

## 4. Residual interface list (named, not expanded)

1. ~~Straight-site embedding (E-ext)~~ — **discharged** (`STRAIGHT-SITE-EMBEDDING-PROOF.md`): the
   abstract refined dual is a simplicial closed disk, its faces are empty-circle polygons, a fixed
   uniform triangulation makes it a subcomplex of one planar Delaunay triangulation, the straight map
   is an embedding by compact/Hausdorff, and Jordan gives image = closed region of the 9-cycle, hence
   hubs strictly inside, P simple, no holes, no exterior triangles — all as conclusions.
2. **Hub-edge bridge** (P3): conditional on the C450 capacity certificate (Part 1 verdict).
3. **Inward-representative bound** `|c| ≤ √(1−r²)` used by VORONOI §3 and the new switch-uniqueness
   lemma: comes from C451/C464 (outside this lane).
4. **Realizability of q ≥ 1 classes**: not needed after the exclusions, but recorded as unproved in
   `AUDIT…` Part 2.
5. **Global (E)** for the central-face interface (from `C900-INDEPENDENT-CHECK.md`): still only
   box-certified.
6. Not needed (checked): "hub ∈ conv(ring centres)" as an input — the chain uses hub cells ⊆ `int D`
   plus hub cell ⊆ `B(h,r)`; note this is *not* the same as (E-ext)'s "hubs inside `P`", which is
   geometric and remains obligation 1.

**Repro**: `py -3 -B -X utf8 research-2026/team-current/r20-gluing/graph_interface_check.py` ;
`py -3 -B -X utf8 research-2026/team-current/r20-gluing/straight_site_control.py`.
