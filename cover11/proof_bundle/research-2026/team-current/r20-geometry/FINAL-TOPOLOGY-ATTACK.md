# FINAL-TOPOLOGY-ATTACK — adversarial check of the assembly interfaces (§§1–4)

**Verdict: NO GAP FOUND** in the three named interfaces

* boundary switch → interior vertex,
* "partial global Delaunay faces still form a disk",
* skip-one chord ear counting,

subject to the proved inputs listed in §5 (C450 atom + C451/C464, the arc ledger of
VORONOI-BOUNDARY-REDUCTION with repairs R1a/R1b/R2/N1, C802 hub edge, ring locality,
NO-FOUR-RING-COMMON-POINT, TWO-TRIPLE-CAPACITY, FIVE-RING-STAR-EXCLUSION). I did **not**
re-derive the C450 atom (declared input) and ran **no numerics**. For every step I give the
analytic reason myself; where the source text asserts a step without proof (the half-width
bound, the second endpoint of a switch facet, the identification of the restricted Delaunay
complex), I supply the missing argument, so nothing below rests on "the source says so".

Notation: `D` unit closed disk, `S¹=∂D`, congruent disks of radius `r ≤ R₀=19/50`, `c_i =` sites,
`I_i = S¹ ∩ B(c_i,r)`, `V_i =` closed nearest-site (Voronoi) cell, `∂D`-intersecting disks are
**boundary disks** (nine of them), the other two are **hubs** `h_1,h_2` with `|h_j|+r<1`.

---

## 0. The obligation and the falsification target

Chain under attack (assembly §§1–4):

```
arbitrary 11-disk cover at r<R*
  → (C922: R*<T<19/50) work at r≤R0
  → 9 boundary disks + 2 strict interior hubs, inward-root representative   [C450+C451+C464]
  → ownership rebuilt: 9 essential cyclic arcs, only adjacent overlaps, no triple overlap
  → clipped Voronoi cellulation of D, cell-spoke dual disk
  → embedded refinement / straight realization
  → two fans, hub degrees sum 13−q, q≤1
```

A **gap** would be one of:
(G1) a switch whose two-cell facet does not reach an interior primal vertex (so the outer dual
cycle would not be made of nine switch edges, or the dual disk would have a 2-gon/parallel edge);
(G2) a restriction of the Delaunay complex to "faces with primal vertex in int D" that is not a
disk, or that carries edges not realized by clipped facets (so the clique/ear counts would apply
to objects with no metric meaning);
(G3) a failure of the "every skip-one chord cuts an empty short-side ear" count, e.g. a hub on the
short side that the count does not see, or a triangle in the long side that does not consume two
original cycle edges.

Each is refuted below.

---

## 1. Boundary switch → interior vertex  (G1)

**Claim S.** In the inward-root representative, for every switch point `p_i` (tie of the
consecutive ring cells `i`, `i+1` on `S¹`) the clipped facet
`F_i = (V_i ∩ V_{i+1}) ∩ D` is a nondegenerate segment whose one endpoint is `p_i` and whose
other endpoint lies in `int D` and is an interior primal vertex (≥3 cells tied there).

**Proof.**

1. `F_i` is convex and lies in the bisector line `L_i` of `c_i,c_{i+1}`, hence is a point or a
   segment. `p_i ∈ F_i`, and at `p_i` the two sites are nearest with common value `ρ_i ≤ r`,
   all other sites strictly farther (a third boundary disk would be a triple overlap on `S¹`,
   excluded by the ledger; a hub satisfies `|u-h| ≥ 1-|h| > r` for `u ∈ S¹`). By continuity the
   same strict separation holds for every point of `L_i ∩ D` in a small neighbourhood of `p_i`,
   so such points lie in `V_i ∩ V_{i+1}`.
2. `L_i` is a **secant** of `S¹`, not a tangent: `dist(0,L_i) = | |c_i|²-|c_{i+1}|² | /(2|c_i-c_{i+1}|) ≤
   (|c_i|+|c_{i+1}|)/2 ≤ sqrt(1-r²) < 1`, using the inward-root norm bound. A tangent bisector
   would require `c_{i+1}-c_i ∥ p_i`, which forces `|p_i-c_i| = |p_i-c_{i+1}|` with the sign of
   `|x-c_i|²-|x-c_{i+1}|²` *not* changing across `p_i` on `S¹` — contradicting that `p_i` is an
   ownership switch. Hence exactly one of the two rays of `L_i` from `p_i` enters `int D`, and by
   step 1 a positive-length piece of it lies in `F_i`: `F_i` is a segment `[p_i,z]`, `z ≠ p_i`.
3. `z ∉ S¹`. If `z ∈ S¹` then `z ∈ V_i ∩ V_{i+1}` (closedness) makes `z` a nearest tie of the
   pair on `S¹`, i.e. a switch of the pair `(i,i+1)`; but an adjacent pair has **exactly one**
   switch: on a positive-length overlap the affine function `f(u)=|u-c_i|²-|u-c_{i+1}|²`
   restricted to the overlap arc is strictly negative at one end and strictly positive at the
   other (the far arc endpoint of one disk lies in the interior of the other's arc, hence its
   distance to the other centre is `< r`), `f` has at most two zeros on the whole circle, and two
   zeros inside the overlap would restore the endpoint signs; so exactly one zero (tangency is
   excluded by the sign change; the zero-overlap/touching case has the single common endpoint as
   the unique tie). Hence `z = p_i`, contradicting `z ≠ p_i`.
4. Therefore `z ∈ int D`. At `z`, all sites tied for the minimum are nearest, and `i,i+1` are
   among them; since `z ∈ D` is covered, the nearest value is `≤ r`, so every tied site is at
   distance `≤ r` from `z`. If only `i,i+1` were tied, then (step 1, strictness) the facet would
   continue through `z`, contradicting that `z` is an endpoint. Hence at least a third cell is
   tied at `z`: `z` is an interior primal vertex. ∎

**Consistency with the outer cycle.** Each adjacent ring pair contributes exactly one switch
(step 3) and these nine switches are pairwise distinct (a common point of two switches would be a
triple overlap on `S¹`), so the nine edges dual to the facets `F_i` are exactly the cycle of the
nine ring cells. The edge dual to `F_i` has exactly one incident dual face, namely the face of
`z`: the global Voronoi edge of the pair may continue *outside* `D` beyond `p_i` (giving Delaunay
faces with circumcentres outside `D`), but inside `D` the facet ends at `z`. Hence the nine
switch edges are boundary edges of the dual disk, each carrying exactly one interior face. ∎

**Degeneracies.** touching arcs (`o_i=0`, `ρ_i=r`) — allowed, the crossing argument is
unchanged; positive overlap (`ρ_i<r`) — allowed; tangent bisector — impossible (step 2);
second boundary endpoint — excluded (step 3); triple tie on `S¹` — excluded by the ledger;
several distinct switches for the same pair — excluded; hub nearest on `S¹` — impossible;
zero-length facet — impossible by step 1. ∎

---

## 2. "Partial global Delaunay faces still form a disk"  (G2)

**Claim D.** Let `K` be the Delaunay subdivision of the eleven sites (projection of the lower
hull of `(c,|c|²)`), and let `K_D ⊂ K` be the sub-complex of faces whose Voronoi vertex lies in
`int D`, together with the nine switch-adjacent ring-ring edges. Then

 (i) as an abstract complex, the polygonal part of `K_D` is the cell-spoke dual disk of the
      clipped cellulation;
 (ii) no edge of that polygonal part lacks a positive-length clipped facet; the diagonals added
      when triangulating a face are *not* Delaunay edges (a non-consecutive pair of a cocircular
      face has zero-length primal facet) but each still carries a genuine common nearest point
      inside `D`, namely the face's Voronoi vertex, which is exactly what the locality-based
      clique/ear counts use;
 (iii) its straight realization is non-crossing, hence homeomorphic to an abstract disk with the
      nine ring cells as its boundary cycle and both hubs interior.

**Proof.** Every site is a vertex of `K` (the plane `z=2c·x-|c|²` supports the paraboloid only
at `c`), and the cells of `K` are strictly convex cocircular polygons, so no vertex lies in the
relative interior of a subdivision edge and the straight realization is a genuine planar
subdivision of `conv{sites}`.

*Face bijection.* Faces of the cell-spoke dual ↔ interior primal vertices of the clipped
cellulation ↔ Voronoi vertices in `int D` ↔ faces of `K_D`. A Voronoi vertex is a point where
`m ≥ 3` distinct sites are tied for the nearest distance; its incident sites are distinct points
of one circle, hence in strictly convex cyclic position, giving one simple dual face (locality of
nearest-site comparison along `x+tv` gives every incident cell a positive sector, no repeated
dual vertex). No two distinct Voronoi vertices carry the same site set (distinct non-collinear
sites have at most one common nearest point), so the bijection is injective; and no Voronoi
vertex lies on `S¹` (that would be a triple tie on `S¹`, excluded by the ledger).

*Edge bijection (polygonal part).* Dual edges ↔ pairs of cells sharing a positive-length
clipped facet ↔ **consecutive pairs of a selected cocircular face** (i.e. genuine Delaunay
edges). The nine switch edges are interior-endpoint edges by Claim S.

* (⊇) Let `F = (V_i ∩ V_j) ∩ D` be a positive-length clipped facet. Then `F` is contained in
  the global bisector facet of the pair, so `(i,j)` is a genuine Delaunay edge, and `F` has an
  endpoint at an interior primal vertex `z`: an endpoint on `S¹` would be a nearest tie of
  `(i,j)` there, hence (by the ledger for non-adjacent labels, by uniqueness of the switch for
  adjacent labels) only the switch of an adjacent pair, whose *other* endpoint is interior by
  Claim S. At `z` the two cells are consecutive in the cyclic order (their facet emanates from
  `z`), so `i,j` are consecutive sites of the Delaunay face of `z`, and that face is selected
  (`z ∈ int D`). Hence `(i,j)` is a polygon edge of `K_D`.
* (⊆) Conversely let `(i,j)` be an edge of a selected face, i.e. `i,j` are **consecutive** in
  the cyclic order of the face's cocircular sites. Then the Voronoi facet of the pair is the
  segment/ray on their bisector emanating from the face's circumcentre `z`; since `z ∈ int D`,
  that facet meets `int D` in a positive-length piece, which is a clipped facet, i.e. a dual
  edge.

The essential point — and the inference that must **not** be made — is that *consecutiveness in
the face* (equivalently: being a genuine Delaunay edge) is what produces the positive-length
facet. A common nearest point alone does not: for a non-consecutive pair of a cocircular face
(a triangulation **diagonal**), both sites are nearest at `z`, yet the pair's facet degenerates
to the single point `z` (zero primal edge length), so it is not a Delaunay edge and not a dual
edge. Diagonals therefore carry locality (a common nearest point at distance `≤ r`, all the
clique/ear counts need) but never a strict positive-length estimate. ∎

*Disk.* The cell-spoke construction (choose an interior point per cell and per positive facet,
join by radial spokes) is an embedded graph: spokes in one convex cell are disjoint, cells have
disjoint interiors, two cells share at most one facet (convexity + one bisector). Removing the
collar (the nine boundary sectors, one per ring cell — a ring cell has exactly two switch facets,
adjacent to its single arc, and no other facet touches `S¹`) leaves a disk whose interior faces
are the interior primal vertices and whose boundary cycle is the nine ring cells connected by the
nine switch edges. By the bijections above this abstract disk is `K_D`; its straight realization
is a planar drawing of it, and a planar drawing of an abstract disk is a disk. ∎

**Degeneracies.** cocircular faces of order ≥ 4 — fine (strictly convex polygon, triangulated;
retaining the hub-hub edge is possible because that edge is an edge of the polygon whenever both
hubs are among the tied sites); interior vertex with three ring cells + both hubs (degree 4/5) —
fine; four ring cells at one interior vertex — excluded by NO-FOUR-RING-COMMON-POINT (four
common disks put all four arcs into `S¹∩B(p,2r)`, and `π ≤ asin(2r)+5asin(r) < π` at `r≤R₀`), so
every cocircular face has at most three ring sites; ring-ring pairs at cyclic distance ≥ 3 —
cannot share a clipped facet (ring locality: their disks would intersect at a point of `D` at
distance `≤ r`, and `π ≤ asin(2r)+5asin(r) < π` excludes it), so they never appear in `K_D`;
collinear sites — harmless, the subdivision keeps every site a vertex and faces stay strictly
convex; degree-2 interior vertices — impossible (a point where only two cells meet forces the
facet to continue through it); zero-length edges — suppressed and never counted; a Voronoi edge
from a switch to a second boundary point — excluded by Claim S. ∎

**Why this answers the specific worry.** "Selecting part of the global Delaunay faces" cannot
create a non-disk: the selection criterion (circumcentre in `int D`) is exactly the set of primal
vertices of the clipped cellulation, so the selected complex *is* the dual disk; and its polygon
edges are genuine Delaunay edges whose facets meet `int D` in positive length (edge bijection
above), so no positive-length/dual edge is imported from outside `D` or invented. Triangulation
diagonals are the only added edges; they are explicitly *not* Delaunay edges (zero primal edge
length — the sharp distinction the edge bijection now makes), yet each still carries a common
nearest point in `int D`, which is all the locality/clique counts use, and they are never used
in a strict positive-length estimate. Conversely no dual edge is lost: every interior primal
vertex is a Voronoi vertex in `int D`, hence a selected face. The only information deliberately
*not* used is the global Delaunay structure outside `D` (vertices with circumcentre outside
`D`), which is exactly what the assembly says it does not assume.

---

## 3. Skip-one chord ear counting  (G3)

**Claim E.** In the triangulated dual disk of §2, every ring-ring edge of cyclic label distance 2
("skip-one chord") cuts an empty short-side ear: the short side contains exactly the intermediate
ring vertex and no hub. Consequently the skipped labels form an independent set, ears cannot share
an edge, and the q-ear core has hub degree sum `13-q` with `q≤1`.

**Proof.**

1. *Ring-ring edges have label distance ≤ 2.* Ring locality: if ring disks `i,j` intersect, their
   full arcs lie in `S¹∩B(p,2r)` (triangle inequality from a common point `p`), an arc of
   half-width `≤ asin(2r)`; label distance `≥ 3` would place ≥ 4 complete arcs in it, giving
   `π ≤ asin(2r)+5asin(r) < 3 < π` at `r ≤ R₀`. So every ring-ring edge is a cycle edge or a
   skip-one chord.
2. *Every ring-only triangle uses two cycle edges.* Three ring cells meeting at one primal vertex
   have pairwise intersecting disks (the vertex is within `r` of each); by step 1 their labels are
   pairwise at cyclic distance `≤ 2`, and the only such triples are consecutive
   (`(j,j+1,j+2)`): three cyclic gaps are positive integers summing to 9, and if none is 7 then
   some pairwise distance is `≥ 3`. A consecutive triple has exactly two cycle edges.
3. *Hub side.* The hub-hub edge exists (C802) and is a chord of the triangulated dual disk; a
   skip-one chord is also an edge, so by planarity the hub-hub edge does not cross it: both hubs
   lie on the same side (no vertex lies in the relative interior of an edge in the abstract
   complex; the straight realization is planar by §2(iii)).
4. *Counting.* Suppose both hubs lie on the short side of the skip-one chord `(i,i+2)`. Then the
   long side is a sub-disk with the eight ring vertices `i+2,i+3,…,i+8,i`, no hubs, and no other
   vertices; it is triangulated, hence has `8-2 = 6` triangles. By step 2 each needs two
   original cycle-edge incidences, i.e. 12 incidences. The original cycle edges available inside
   are exactly the seven boundary edges `(i+2,i+3),…,(i+7,i+8),(i+8,i)`; each is a boundary edge
   of the disk, hence incident to exactly one triangle of the sub-disk: 7 incidences available.
   `12 > 7`, contradiction. So the short side carries no hub; its only vertex is the intermediate
   ring, and the chord plus the two boundary cycle edges bound a single triangle — an ear. ∎
5. *Consequences.* Two ears with adjacent skipped labels have chords `(i-1,i+1)` and `(i,i+2)`
   whose endpoints interleave on the outer cycle: they would cross, impossible; so skipped labels
   are independent. Two disjoint-label ears are excluded by TWO-TRIPLE-CAPACITY
   (`π ≤ 2asin(2r)+3asin(r) < π` at `r ≤ R₀`, union-measure argument on the two triple windows);
   two ears sharing a corner ring make that ring intersect four others, and FIVE-RING-STAR
   (`π ≤ acos(53/775)+4asin(R₀) < 3.07 < π`) excludes it. Hence `q ≤ 1`. Removing an ear is a
   clean boundary collapse: the short side is a sub-disk with exactly the three boundary vertices
   `i,i+1,i+2` and no interior vertex, its triangulation is therefore the single face
   `(i,i+1,i+2)`, and at the *boundary* vertex `i+1` the whole interior half-neighbourhood is
   occupied by that face, so `i+1` has degree exactly two and no hub neighbour; deleting it (the
   chord `(i,i+2)` is already an edge) leaves a disk. Iterating, the core is a disk on `9-q` ring
   vertices plus the two hubs, and every face of it involves a hub. Its boundary is traversed by
   the two hub links: the link of a hub with the other hub deleted is the path between the two
   ring neighbours `u,v` of the hub-hub edge, and by step 4 all its ring-ring edges are boundary
   edges of the core; the two hubs use the two complementary boundary paths (every core boundary
   edge has exactly one incident core face), giving two fans plus the two triangles on the
   hub-hub edge. Degrees: the two paths share exactly the endpoints `u,v`, so
   `m_1 + m_2 = (9-q) + 2` and the degree sum is `(m_1+1)+(m_2+1) = 13-q`, with `m_j ≥ 2` because
   the two hub-edge triangles have distinct ring neighbours (`u=v` would put the same ring vertex
   on both sides of the hub-hub edge). ∎

**Degeneracies.** skip-one chord on the boundary of the *unrefined* disk — impossible: the outer
cycle consists of cycle edges only; a second skip-one chord sharing the short side — would put
two vertices in it, contradicting emptiness; artificial (triangulation) diagonals — they are
edges of the triangulated disk and the counting applies to them (each triangle they bound still
has a genuine common nearest point, its primal vertex, so step 2 applies); a skip-one chord whose
long side has hubs — then the counting above is vacuous but the short side is still an ear by
step 4 applied to the *other* side (both hubs are never on the short side); a ring-only triangle
with a repeated label — impossible (three distinct tied sites); the q=1 case — one skipped
vertex, `m_1+m_2 = 10 = (9-q)+2`, degree sum 12, and the two fan paths use the unique skip-one chord as a
boundary edge. ∎

---

## 4. Complete degeneracy ledger for §§1–4

| degeneracy | where it could bite | status |
|---|---|---|
| touching arcs `o_i=0` (`ρ_i=r`) vs positive overlap | switch structure, facet entry | allowed; unique switch either way (§1.3) |
| ring cell owning a point arc | 9 arcs essential, dual degree | excluded: `2asin(R₀) < π/4` and `Σw_i=2π` (§5 item A2/A3) |
| bisector tangent to `S¹` at a switch | facet enters `D` | impossible in inward-root rep (`dist(0,L_i) ≤ sqrt(1-r²)<1`) |
| second boundary endpoint of a switch facet | "switch → interior vertex" | excluded by uniqueness of the switch (§1.3) |
| triple/multiple tie on `S¹` | switches distinct, degree 3 | excluded by the arc ledger |
| four boundary disks with a common point | faces with ≥4 ring sites | excluded (NO-FOUR-RING-COMMON-POINT) |
| cocircular interior vertex (order ≥ 4) | triangulation, repeated vertices | fine: strictly convex cocircular polygon, distinct sites |
| interior vertex of degree 2 | "every interior vertex degree ≥ 3" | impossible: a two-cell contact forces the facet to continue |
| zero-length Voronoi edges | Euler/incidence counts | suppressed, never counted |
| hub nearest on `S¹` | switch-involving-hub | impossible: `|u-h| ≥ 1-|h| > r ≥` covering distance |
| hub-hub facet degenerate/point | two fans | excluded by C802 (proved input); two convex cells share one segment |
| ring-ring facet at label distance ≥ 3 | clique/ear counts | excluded by ring locality |
| phantom Delaunay edge from outside `D` | "partial faces" claim | cannot appear in a selected face: any visible edge (or diagonal) has a nearest point in `int D` (§2 edge bijection) |
| collinear sites / non-generic Delaunay | straight realization | all sites remain lower-hull vertices; faces strictly convex; drawing stays planar |
| two skip-one chords | ear count, q | excluded: adjacent skipped labels cross; two ears excluded by capacity arguments |
| skipped vertex with hub-ring edges | core degree count | impossible: at a skipped (boundary) vertex the whole interior half-neighbourhood is the ear face, so it has degree 2 |
| artificial diagonals counted as metric edges | ear count uses "two cycle edges" | correct usage: diagonals are legitimate edges of the triangulated disk with a real common nearest point, and are *not* counted as original cycle edges |

## 5. Proved inputs used, with exact scope

* **A1. C450 atom** (declared input, not recomputed): ten boundary disks + one arbitrary other
  disk cannot cover at radius `R₀`, used three times — `m ≠ 10`; the two non-boundary disks are
  strictly interior and indispensable (replacement by a tangent boundary disk would give the
  excluded configuration); the hub-edge argument (non-adjacent hub cells → `e ≤ 3r-1 ≤ 7/50` →
  the nine enlarged ring disks cover `S¹` and `S(h_1,R₀)` → capacity contradiction).
  *Scope check I did perform:* the enlarged configuration meets the atom's quantified domain
  (radius `R₀` exactly, all nine disks meet `S¹`, centre norms in `[1-R₀,1+R₀]` via the inward
  roots, hub offset `e ∈ [0,7/50]`, both circles covered).
* **A2. The half-width bound** `I_i` has width `≤ 2asin(r)`: `half-width = arccos((1+d²-r²)/(2d))`
  for `d=|c_i| ∈ [1-r,1+r]`, maximised at `d=sqrt(1-r²)` (the polar/inner-root distance) with
  value `asin(r)`; I verified this maximum myself, so §1's "one arc of width ≤ 2asin(r)" (which
  the reduction text merely asserts) is self-contained. Numerically `2asin(R₀)=0.7795 < π/4`.
* **A3. Nine boundary disks / at least nine:** the arcs cover `S¹`, so `Σh_i ≥ π` (subadditivity
  with overlaps), and `Σh_i ≤ m·asin(R₀)`, giving `m ≥ π/asin(R₀) > 8`.
* **A4. Arc ledger** (VORONOI-BOUNDARY-REDUCTION + review): nine essential cyclically ordered
  arcs, strict endpoint order, only adjacent overlaps, no triple overlap, exactly nine distinct
  switches, one connected nearest arc per ring, inner-root representative preserves the arcs and
  the whole-disk covering. The review's repairs are necessary and I re-checked them: R1a (strict
  endpoint signs come from the overlap being positive-length, not from arclength `<π`), R1b (`f`
  has at most two circle zeros, so two zeros inside the overlap would equalise the endpoint
  signs), R2 (the two switch sites are *strictly* nearest at the switch for `o_i>0`; for `o_i=0`
  use `ρ=r`; every other site is `> r`), N1 (`H ∩ V_i = ∅`; `cl H ⊆ V_1 ∪ V_2`).
* **A5. C802 (hub edge)** — used for the two-fan split and for §3 step 3.
* **A6. Ring locality / NO-FOUR-RING-COMMON-POINT / TWO-TRIPLE-CAPACITY /
  FIVE-RING-STAR** — used for label distance ≤ 2, faces with ≤ 3 ring sites, and `q ≤ 1`
  respectively; each is a union-measure inequality on the closed radius range `r ≤ R₀`, and I
  re-read each statement against the use made of it here.

**Not verified here / out of scope:** the internal interval arithmetic of the C450 atom; the
metric exclusions of assembly §5; C891/C921/C922; the q0(6,7) oracle reduction of §6. (Per the
lead, C921 now covers the full canonical simplex oracle, so the earlier "q0(6,7) metric still
open" reading is superseded; this note is topology-only and depends on neither reading.) This
note certifies topology only; it yields no radius bound.

## 6. Residual risk and what would falsify the interfaces

* The only non-elementary inputs are A1 (C450) and A4 (arc ledger). If either fails, §1–§3 fail
  with it; both are stated with their own controls elsewhere and I did not re-certify them.
* A counterexample to Claim S would need a bisector secant of `S¹` through a switch whose inward
  ray terminates at another point of `S¹` without a third cell being tied there — impossible by
  §1.3–1.4. A counterexample to Claim D would need a Delaunay face with interior circumcentre
  containing an edge whose two sites are not co-nearest inside `D` — impossible by the definition
  of the face's site set. A counterexample to Claim E would need both hubs on the short side of a
  skip-one chord with the long-side count still closing, or a ring-only triangle with a pairwise
  distance ≥ 3 — impossible by §3.2 (clique lemma) and §3.4 (12 > 7).
* Practical caveat for downstream use: the counting arguments use *distinct vertices* and *no
  repeated vertex in a face*; both are established above for the clipped cellulation and its
  Delaunay realization. Any later argument that replaces the hub edge or the artificial diagonals
  by independently chosen incidences must re-check these two properties.

Evidence paths (read-only): `lead/UNRESTRICTED-PROOF-ASSEMBLY.md` §§1–4,
`lead/DUAL-DISK-INTERFACE-AUDIT.md`, `lead/UPSTREAM-ARC-TOPOLOGY-AUDIT.md`,
`closure-geometry/HUB-ADJACENCY-FINAL-AUDIT.md`, plus the sources named in §5
(`solo-20260922/N11-LOW-RADIUS-REDUCTION.md`, `INNER-ROOT-DOMINANCE.md`,
`lead/VORONOI-BOUNDARY-REDUCTION.md`, `flash-structure/REVIEW-VORONOI-BOUNDARY-REDUCTION.md`,
`lead/TWO-TRIPLE-CAPACITY.md`, `lead/FIVE-RING-STAR-EXCLUSION.md`,
`lead/HUB-ADJACENCY-DUAL.md`). No file outside `r20-geometry/` was modified; no claim registered.
