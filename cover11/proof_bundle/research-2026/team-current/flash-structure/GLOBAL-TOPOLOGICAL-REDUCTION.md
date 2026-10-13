# Global finite combinatorial reduction of the ring–hub topology (9 + 2 branch)

Author: flash-structure. Requested by lead (2026-09-24): make C798's finite combinatorics plus the
degenerate refinement into a **global interface**, spell out why the dual is a regular cell complex
(each ring cell connected to `∂D`, all cells convex, boundary cycle of length 9), add the core
two-fan classification, and state one citable **global finite combinatorial reduction** (not a finite
metric claim). Independent derivation; own instruments; the geometric premises are reduced to the
minimum needed.

## 0 Premises (all that is used)

(P1) Nine boundary disks of radius `r <= 19/50` meet `∂D`, their arcs are essential, cyclically
ordered, only neighbouring arcs overlap and multiplicity `<= 2` (arc ledger, unconditional in this
branch); the two remaining disks are strictly interior (`|h| + r < 1`, from the 9+2 reduction);
the eleven disks cover `D`.
(P2) Locality lemma (C799): intersecting ring disks have cyclic index distance `<= 2`; three ring
disks with a common point are consecutive.
(P3) Hub-edge bridge (C797, conditional on the C450 capacity certificate): the two hub cells share an
edge (`d = 1`).
**No inner-root assumption, no symmetry, no metric hypothesis, no enumeration beyond finite
combinatorics.**

## 1 Interface lemma — the dual is a regular cell complex on a disk

**(1.1) The clipped primal.** For each centre `c`, put `V(c) = {x : |x−c| <= |x−c'| ∀c'}` and clip with
`D`. Convexity: every `V(c)` is closed convex, `D` is convex, so every cell `V(c) ∩ D` is closed convex
and connected. Interiors are disjoint and their union is `D` (the nearest-centre rule; the covering is
used only to know that every cell is nonempty, see below). **Each ring cell meets `∂D` in a nondegenerate
arc**: the nearest-centre arcs of `∂D` are delimited by the nine distinct switch points (Voronoi note
§1), and nine distinct points on a circle cut it into nine nondegenerate arcs; the points of one such
arc lie in a single cell (the nearest one there). Each **hub cell is inside `int D`** (Voronoi note §2)
and contains its centre, hence has nonempty interior; each ring cell has nonempty interior relative to
`D` because it contains a nondegenerate arc of `∂D`. So all 11 cells are 2-dimensional and the
cellulation is a **regular cell complex** whose underlying space is the disk `D`: the 1-cells are the
Voronoi edges inside `D` (segments, since cells are convex polygons) and the 0-cells are their
endpoints plus the nine switch points on `∂D`; the 9 switch points have degree 3 (each has two boundary
arcs and one interior edge, C781).
*Nothing here uses the inward-root replacement*: the argument needs only that the ring centres are
distinct and their cells meet `int D`, which holds for an arbitrary centre configuration. (The
inward-root replacement remains useful for other purposes, e.g. `V_h ⊆ B(h,R)` with the enlarged
radius.)

**(1.2) The dual.** The dual cell complex has one vertex per cell (9 ring + 2 hub), one edge per
interior primal edge (Voronoi adjacency) and one face per interior primal vertex (additionally the
boundary of the dual uses the nine primal edges that have one endpoint at a switch point: each such
edge is incident to exactly one dual face, hence is a boundary edge). Consequences:
* the nine ring vertices lie on the boundary of the dual, in the cyclic order of their `∂D` arcs;
* the two hub vertices are interior (their cells avoid `∂D`);
* the boundary cycle of the dual has length `9` with edges exactly the nine distance-1 ring-ring
  adjacencies `(i,i+1)`; in the trivalent case `E = 21`, `F = 11` (and `3F = 2E − b` gives `b = 9`,
  consistent);
* the dual is connected and is a regular cell complex on a disk (dual of a disk cellulation).

**(1.3) Degenerate (non-trivalent) configurations — corrected (lead review).** A `k`-fold interior
primal vertex `x` has `k` incident cells; each of them contains `x` (it is covered, say `|x−c| <= r`,
and `x` is nearest for all of them, so `|x−c_t| <= r` for each), hence **all ring sites of that face
pairwise satisfy the locality restriction of (P2)** — and therefore so does every diagonal added inside
such a face. Refine every face of degree `> 3` by *any* triangulation of its own vertices: the
refinements are interior to disjoint faces, so they glue to a global simple refinement of the dual, and
the boundary cycle and the nine boundary edges are untouched.

**A refinement can create new ring-only faces (the earlier claim that it cannot is FALSE).** Control:
the 4-fold vertex with cells `{h, i, i+1, i+2}` is a quadrilateral dual face `(h,i,i+1,i+2)`; the
diagonal `(i,i+2)` splits it into `(h,i,i+2)` and the **ring-only** triangle `(i,i+1,i+2)`. Such an
artificial ear represents a zero-length primal edge and is not a genuine ring-only Voronoi vertex.

**What is actually true and sufficient.** (i) every added ring-ring edge obeys the same locality rule,
so the refined complex satisfies the same rules R1–R5, in particular every ring-only face of the
refined complex is still a consecutive triple (its three ring sites have all pairwise index distances
`<= 2`, and a ring-only face with `>= 4` vertices would need a `>= 4`-clique of `C_9^2`, whose clique
number is 3); (ii) hence **the ear/fan classification applies to the refined complex with its own
combinatorial `q` and hub degrees**, and degenerate configurations are covered **without any claim that
`q` is preserved** by refinement; (iii) `q`, `K = k_1+k_2` and the degrees are *refinement-dependent*
combinatorial quantities, which need not agree with those of the original positive-length graph;
(iv) added diagonals must not be fed into strict positive edge/degree estimates.

*Remark (a refinement that avoids new ring-only faces always exists, if one prefers).* For a face with
`>= 1` hub and `k > 3` vertices, triangulate it as the fan from one of its hubs; every sub-triangle then
contains that hub, so no ring-only face is created. When the face contains **both** hubs, the hub-hub
edge is one of its boundary edges (it is an actual primal edge, `d = 1`); keep it, and use diagonals
from one hub only, e.g. for the pentagon `(h,h',i,j,k)` the diagonals `(h,i),(h,j)` give the triangles
`(h,h',i),(h,i,j),(h,j,k)` — all containing `h`, with `(h,h')` preserved. A face with no hub is
ring-only, hence already a triangle (`q`-faces), so no refinement is needed there.

## 2 Combinatorial engine: chords cut empty ears

(Pure counting, after the lead's observation; independently re-derived and also verified exhaustively.)

Let `(i,i+2)` be a skip-one chord of the dual (an edge between ring cells at distance 2). By (P3) the
hub-hub edge keeps both hubs on one side of the chord. If both hubs were on the **short** side (whose
boundary vertices are `i, i+1, i+2`), the **long** side would be an 8-gon with the eight ring vertices
`{0,2,3,...,8}` and no interior vertex, triangulated by ring-only faces only. By (P2)/(P3) every such
face is a consecutive triple `(j,j+1,j+2)`, which contains **two original 9-cycle edges**
`(j,j+1),(j+1,j+2)`. Within the 8-gon only **seven** original edges are available (the eighth boundary
edge is the chord itself), and an original edge is a boundary edge of the 8-gon, hence lies in exactly
one face. A triangulation of the 8-gon has **six** faces and would need at least `2·6 = 12 > 7` such
edges. Contradiction. (Independent check: of all `132 = Catalan(6)` triangulations of that 8-gon, not
one has all faces consecutive — `out/run8_topology_skeleton.txt`.)

Therefore each skip-one chord cuts out an **empty ear**: the short side is exactly the ring-only
triangle `(i,i+1,i+2)`, no hub on it. The skipped (middle) vertices of two ears can never be adjacent —
the corresponding chords would cross in the planar dual — so the skipped set `S` is an independent
subset of `C_9`.

### 2b Two disjoint triple clusters are impossible ⟹ `q <= 2` (lead's `TWO-TRIPLE-CAPACITY.md`, verified)

Write `A = asin r`, `B = asin(2r)`; for `r <= 19/50` one has `A < 0.4`, `B < 0.9` by the alternating
Taylor bound `sin x >= x - x³/6` (`sin(0.4) >= 0.3893 > 0.38`, `sin(0.9) >= 0.7785 > 0.76`).

*If a triple of ring disks has a common point `p`, all three of its arcs lie in `J_p = ∂D ∩ B(p,2r)`,
of length `<= 2B`* (triangle inequality). All steps below are union-measure, so overlaps only help; no
Voronoi input is needed.

**Two-triple lemma.** Two triples with **disjoint** label sets, common points `p` and `q` (possibly
equal), give six arcs inside `J_p ∪ J_q` and three remaining arcs of length `<= 2A` each, hence
`2π <= |J_p| + |J_q| + 6A <= 4B + 6A`, i.e. `π <= 2B + 3A < 1.8 + 1.2 = 3 < π` — contradiction. ∎
(Fully rational certificate; `π > 3` is classical.)

**Consequences.**
1. A ring-only face — genuine *or* artificial (refining a degenerate face: all its cells contain the
   original higher-order vertex `x`, so those disks share `x`) — is a triple with a common point. So two
   ears with disjoint label triples cannot coexist: their label sets intersect.
2. Skipped labels at distance `1` are impossible (interleaved chords would cross in the planar dual);
   distances `3, 4` are impossible (the triples would be disjoint, excluded above). Hence **any two
   skipped labels are at cyclic distance exactly 2**.
3. No three labels of `C_9` are pairwise at cyclic distance exactly 2 (rotate to `0`; the others must be
   `2` and `7`, mutually at distance `4`). Hence **`q <= 2`**, the classes `q = 3, 4` are globally
   excluded, and `K = 13 - q >= 11`. For `q = 2` the skipped labels are `i, i+2` and the ears share the
   corner label `i+1`.
4. *`q = 2` quantitative form.* The shared arc `I_{i+1} ⊆ J_p ∩ J_q`, the union of the five involved
   arcs lies in `J_p ∪ J_q`, and the remaining four arcs have length `<= 2A`, so
   `2π <= |J_p ∪ J_q| + 8A <= 4B - 2t_{i+1} + 8A`, i.e. **`t_{i+1} <= 2B + 4A - π ≈ 0.1442`** — a
   necessary severe small-arc condition (no contradiction follows from it).

Surviving classes (after §2b alone): `q ∈ {0,1,2}`.

### 2c Five-ring star lemma excludes `q = 2` ⟹ `q <= 1` (lead's `FIVE-RING-STAR-EXCLUSION.md`, verified)

**Star lemma.** No ring disk intersects four or more other ring disks. If it did, then for a point `u`
of any of the five involved arcs, `|u−c_i| <= r + 2r = 3R` (own arc `<= r`; a partner's arc `<= r` plus
`|c_j−c_i| <= 2r <= 2R`, closed disks, tangency included), so the **union** of the five arcs lies in the
window `W = ∂D ∩ B(c_i,3R)`. Its half-width is `arccos((1+ρ²−L²)/(2ρ))` with `ρ = |c_i| >= 1−R`,
`L = 3R = 1.14 > 1`; the cosine argument `(1+ρ²−L²)/(2ρ) = ρ/2 + (1−L²)/(2ρ)` increases in `ρ`, so the
half-width is maximal at `ρ = 1−R` and equals exactly `arccos(53/775) = 1.5023558121 < 1.51`
(certificate: the alternating Taylor partial sum
`S6 = 4157657580296159392266908059543/68428800000000000000000000000000 = 0.06075888486` upper-bounds
`cos(1.51)`, and `S6 < 53/775` by integer cross-multiplication). The remaining four arcs have half-width
`<= A = asin r < 0.39` (`sin(0.39) >= 0.39 − 0.39³/6 = 0.3801135 > 0.38`). Therefore, **in union
measure** (sums over overlapping arcs are NOT bounds and must not be used here — this is exactly the
overlap gap of the overall problem):

```
|S¹| = |∪ all nine arcs| <= |∪ five arcs| + Σ_{remaining four} |I| <= 2·1.51 + 4·2·0.39 = 6.14 < 2π ,
i.e.  π <= |∪ five arcs|/2 + Σ_{remaining four} t_i <= 1.51 + 4·0.39 < π ,
```

a contradiction. Hence every ring disk has at most three ring-intersection partners, and a fortiori
every ring cell has at most three ring neighbours in the dual (cell adjacency implies the two disks
intersect).

**Consequence `q != 2`.** In the `q = 2` class the ears are `{i−1,i,i+1}` and `{i+1,i+2,i+3}`, sharing the
corner label `i+1`; both are Voronoi vertices, so the disks `i−1, i, i+2, i+3` each contain the
corresponding vertex — four ring partners of disk `i+1`, contradicting the star lemma.

**Hence `q <= 1`, `K = 13 − q ∈ {12,13}`, surviving classes `q ∈ {0,1}`.** The single-triple quantitative
condition of `TRIPLE-CLUSTER-NECESSARY.md` (`t >= t0 = π − B − 5A = 0.3292980562` for every label outside
a triple with a common point) is verified too, but is no longer needed since `q = 2` is excluded
directly. **Its derivation must also be read in union measure** (corrected after lead review): if a
triple of disks shares a point `p`, the **union** of its three arcs lies in `J_p`, so
`|∪ triple|/2 <= B` — *not* `Σ_{triple} t <= B`, which can fail because of the adjacent-arc overlaps.
Then `π = |∪ all nine|/2 <= |∪ triple|/2 + Σ_{other six} t <= B + Σ_{other six} t`, and bounding five of
the six by `A` gives `t >= π − B − 5A = t0` for the remaining one.

## 3 Core and the two-fan classification

Delete the `q` ears from the dual. What remains is a core which is again a triangulated disk: its
boundary is the `(9−q)`-gon on the surviving ring vertices (with `9−2q` distance-1 edges and `q` chords),
the two hubs are interior and adjacent (the hub-hub edge survives). Counts (re-verified, `d = 1`):
`K = k_1+k_2 = 13 − q`, `q = c` (number of chords = number of ears), `K = 13 − q >= 11` (by §2b), every
core face contains a hub, and the two faces adjacent to the hub-hub edge have distinct third vertices
`u != v`, both ring.

**Forced fan (link proof; the earlier "the hub-hub edge cuts the core into two sub-disks" was WRONG —
its endpoints are interior vertices, so that edge alone does not split the disk; lead review).**
Work in the core, i.e. after deleting the `q` ears.

* The core is a triangulated disk, so the **link of each hub vertex `h_j` is a simple cycle**; it
  contains the other hub `h'` exactly once (the hub-hub edge is a single primal edge, i.e. a single
  dual edge).
* Deleting `h'` from that link leaves a **simple path of ring neighbours** `u = w_0, w_1, ..., w_m,
  w_{m+1} = v` of `h_j`; its endpoints are the two vertices adjacent to `h'` on the link, i.e. exactly
  the third vertices of the two hub-hub faces.
* Consecutive path vertices `w_k, w_{k+1}`, together with `h_j`, span a core face, so `(w_k,w_{k+1})`
  is a ring-ring edge of the core.
* The core has **no interior ring-ring chord**: every distance-2 ring-ring edge was the chord of an ear
  (the map ear ↔ chord is a bijection, since each chord has at most one ring-only endpoint and
  `q = c`), and after deleting the ears those chords are boundary edges of the core.
* Hence every `(w_k,w_{k+1})` is a **boundary edge** of the core, so the path is one of the two
  boundary `u`–`v` arcs; the other hub yields the other arc, and the two arcs together are the whole
  boundary cycle.
* Consequently the faces incident to `h_j` are exactly the fan `(h_j, w_k, w_{k+1})` over its arc plus
  the two hub-hub faces `(h_j,h',u)`, `(h_j,h',v)`; hence `k_j = 1 + (m_j+2) = m_j+3`, consistent with
  `k_1+k_2 = 13 − q`. Every interior vertex of an arc is adjacent to exactly **one** hub: if `w` were
  adjacent to both, the 3-cycle `(h_1,h_2,w)` would bound two faces; and `u != v`, since otherwise the
  3-cycle `(h_1,h_2,u)` would bound two faces, closing a 2-sphere component and leaving no outer
  boundary — impossible for a disk. (Equivalently: in a simple triangulation every 3-cycle bounds at
  most one face.) This also re-proves the count of hub-ring edges: `4 + (9-q-2) = 11 - q`.

**Completeness with respect to higher degeneracies.** Refining first (§1.3) turns any configuration
into a trivalent one that still satisfies R1–R5 (in particular every added ring-ring edge obeys
locality, so ring-only faces stay consecutive triples), hence the finite list below covers degenerate
configurations as well. **No invariance of `q` under refinement is claimed** — `q`, `K` and the degrees
belong to the refined complex and may differ from the positive-length graph. Two caveats: (i) the
refinement uses only diagonals inside existing faces, so the boundary cycle of length 9 and the nine
boundary edges are untouched; (ii) artificial (zero-length) diagonals may not be used in strict
positive-edge/degree estimates.

**Classification.** The data
```
(S subset of C_9, independent, |S| = q <= 2, pairwise skipped labels at distance exactly 2),
{u,v} (the two transition ring vertices = third vertices of the two hub-hub faces),
the assignment of the two hubs to the two paths (2 ways, or 1 with the paths swapped),
```
determine the whole dual triangulation, up to the refinement of degenerate faces of §1.3. This is a
**finite** list (cyclic choices), valid for arbitrary arc overlaps.

## 4 Payoff, scope, and what is not claimed

* Citable statement (global, finite, combinatorial): *in the 9+2 branch, every covering configuration's
  cellulation topology is one of the finitely many two-fan structures above; in particular there is at
  most **one** ring-only face (ear), it is a consecutive triple, and the core is a `(9−q)`-gon with
  two adjacent hubs (`q ∈ {0,1}`).*
* The saved configuration has `q = 0`, `K = 13`. By §2b and §2c the classes `q = 2, 3, 4` are
  **excluded**; the surviving classes are `q ∈ {0,1}` with `K ∈ {12,13}`.
* Remaining gaps (explicitly, so the reduction is not oversold): (i) excluding the class `q = 1`;
  (ii) **the metric lower bound in the `q = 0` class itself** — `q = 0` is *not* the finish line: the
  sharp unconditional lower bound `r_D(11) >= R_stru` within `q = 0` (all metric configurations) is an
  independent, large open obligation; (iii) the two-hub covering criterion (O1 chain) and its
  cover-extendable tip inequalities; (iv) independent review of the C450 certificate, on which the
  hub-adjacency bridge rests. Excluding the remaining class alone would **not** establish the main
  goal.
* Not claimed: any metric statement, any sharp radius, realizability of the `q = 1` class, any
  degree-3-hub restriction, and nothing about the two-hub covering criterion (the O1 chain is untouched).
* The `t0 = 0.3292980562` item (single triple with a common point forces `t >= t0` for every outside
  label) **is** verified here — it comes from `lead/TRIPLE-CLUSTER-NECESSARY.md` and my earlier note that
  I could not reproduce it is corrected; it is simply not needed for `q <= 1` (§2c).
* Premise status: (P2) proved (C799); (P3) proved conditional on the C450 certificate (C802); §1, §2,
  §2b and §3 proved here (analytic; the only enumeration is a non-load-bearing cross-check).

## 5 Reproduction

`py -3 -B -X utf8 research-2026/team-current/flash-structure/tools/run8_topology_skeleton.py`
(8-gon exhaustive check, ear-set enumeration, count identities), evidence
`out/run8_topology_skeleton.txt`. §1 (interface) and §3 (forced fan) are analytic; the lead's
`LOCALITY-TOPOLOGICAL-EARS.md` contains the same counting engine for §2 and the fan statement for §3,
which this file re-derives and extends by the interface lemma and the degeneracy treatment.
