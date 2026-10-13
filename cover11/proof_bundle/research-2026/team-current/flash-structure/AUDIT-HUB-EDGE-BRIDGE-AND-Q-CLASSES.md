# Audit: hub-edge capacity bridge, and the finite q-class topology skeleton

Author: flash-structure. Requested by lead (2026-09-24). Own derivation and own instruments; no import
of the lead's scripts. **No triangle-topology assumption is used in Part 1.** Nothing here is
registered as proved before the checks below.

## Part 1 — the bridge "the two hub cells must share an edge" (lead's proposal, verified)

**Claim (B-adj).** In the 9-ring + 2-hub branch at `r <= 19/50`, the two complete hub Voronoi cells
`V_1, V_2` share an edge (`d = 1`), i.e. `V_1 ∩ V_2` has positive length.

**Hypotheses actually used.** (H1) nine ring disks meet and cover `∂D`, two hubs are strictly interior,
all eleven radius-`r` disks cover `D` (the C450/C451 branch); (H2) the per-single-disk capacity bound of
C450 (`M10-038-EXCLUSION.md` §2–§4: for every `e ∈ [0,7/50]` there are weights with
`Q(t,v,e,±) < B/10` for **every** single disk of radius `R = 19/50` touching `∂D`); (H3) `V_h` is a
nearest-centre cell of a *center-based* Voronoi diagram (radius-independent), `V_h ⊆ B(h,R)`
(Voronoi note §2, with the enlarged radius), hub cells `⊆ int D` (same §2), and N1 (`H ∩ V_i = ∅`) or
rather its elementary form used below. **No arc-ledger, tip, O1 or locality input is needed.**

Steps (each verified):

1. *Enlarge radii to `R = 19/50`.* Disks only grow, so `D` is still covered and the ring disks still
   meet `∂D` (their centres satisfy `| |c_i| − 1 | ≤ r ≤ R`). Voronoi cells are unchanged. Ring centres
   then satisfy `|c_i| ∈ [1−R, 1+R]`, which is exactly the parametrisation domain of the C450
   certificate (`ρ = cos t ± sqrt(R²−sin²t)`, `t ∈ [0, asin R]`, both root signs).
2. *Core.* For `|x| < 1−2R` and any ring centre: `|x−c_i| ≥ |c_i| − |x| > (1−R) − (1−2R) = R`, so the
   open core `K := B(0,1−2R)` is covered by no ring disk (radius `R`).
3. *Core ⊆ hub cells.* `K ⊆ D` is covered by the eleven radius-`R` disks; every core point is covered by
   a hub. If a core point were nearest to a ring centre `c_i` then, being covered, `|x−c_i| ≤ R` ⟹
   `x ∈ B(c_i,R)`, contradiction with step 2. Hence `K ⊆ V_1 ∪ V_2`.
4. *Core inside ONE hub cell.* **Corrected wording (lead review):** the hypothesis is `dim(V_1 ∩ V_2) <= 0`
   (empty or a single point) — *not* "empty interior", which holds for every pair of distinct Voronoi
   cells (their interiors are disjoint), `d = 1` included. Both hub cells are convex and lie in `int D`
   (hence bounded), so `V_1 ∩ V_2`, being convex and contained in their bisector line, is empty, a
   point, or a segment, and `d = 1` is exactly the positive-length case. Under `dim <= 0`, `K \ (V_1 ∩ V_2)`
   is partitioned by the two closed sets `K ∩ V_j`; if both were non-empty, `K \ {p}` (a punctured disk,
   connected) would be split, so `K ⊆ V_j` for one `j`.
5. *Hub is deep.* `K ⊆ V_j ⊆ B(h_j,R)` gives, at the core point opposite to `h_j`,
   `(1−2R) + |h_j| ≤ R`, i.e. **`|h_j| ≤ 3R−1 = 7/50`** — the same `e`-domain as the C450 certificate.
6. *Radial facet lemma.* For any unit `u`, the ray `h_j + s u` leaves `V_j` (bounded, step 5/§2) at
   `q = h_j + t u`, `t = |q−h_j| ≤ R` (since `V_j ⊆ B(h_j,R)`). By `d = 0` the facet at `q` borders a
   RING cell with centre `c`, so `|q−h_j| = |q−c| = t`. With `v = c − h_j` this gives `|v|² = 2t u·v`
   and therefore
   `|h_j + R u − c|² − R² = R² − 2R u·v + |v|² − R² = |v|²(1 − R/t) ≤ 0` (because `t ≤ R`).
   So **`S(h_j,R) ⊆ ∪_{ring} B(c_i,R)`** (every point of the sphere is inside one ring disk), and the
   same computation works for any radius `≥ t`, in particular for `R`.
7. *Capacity.* `∂D` is covered by the nine ring disks of radius `R` (the original arcs cover it), and so
   is `S(h_j,R)` (step 6). Summing the weighted arc integrals over the two circles: `Σ_{i=1}^9 Q_i ≥ B`.
   But (H2) gives `Q_i < B/10` for every single disk, hence `Σ Q_i < 9B/10 < B` — contradiction.
8. Therefore `d = 0` is impossible, i.e. **`d = 1`** ∎

**Verdict.** The bridge is sound as written, conditional on (H1) the branch hypothesis and (H2) the
C450 certificate (itself `proved-interval` with two independent arithmetic kernels, independent review
pending). Notes for the record:

* the bridge uses **nine** rings but the certificate's bound `Q < B/10` is stronger than the needed
  `Q < B/9`; there is slack;
* it does **not** need the inner-root representative (step 1 only uses `|c_i| ∈ [1−r,1+r]`), nor any
  arc-ledger / O1 / locality statement;
* scope-limited sanity check (**only at the saved radius `r = R_struct`; not a general statement**): at
  that radius the bridge's `d = 0` branch would force `|h| ≤ 3R−1 = 0.139951`, while the record hubs sit
  at `|h_0| = 0.149428`, `|h_2| = 0.272977` — consistent with the record configuration being in the
  `d = 1` class (its Delaunay has the hub-hub edge). No numerical claim of this kind is made in general
  (it is not an ingredient of the proof);
* the only place where the argument is *not* purely combinatorial is (H2); everything else is
  elementary convexity/continuity plus `V_h ⊆ B(h,R)`.

## Part 2 — finite q-class topology skeleton (audit of the lead's proposal)

**Rules used.**
* R1: the dual of the clipped cellulation (trivalent case) is a triangulated disk with the nine ring
  cells on its boundary cycle and the two hubs as interior vertices; `E = 21`, `F = 11`, boundary
  length `9` (derived from `v <= 11`, `e <= 21` and `3F = 2E − b`). No plane-Delaunay/hull hypothesis
  is needed — the clipped dual always has this shape.
* R2: every face is a triangle (trivalent); degenerate faces are refined by diagonals (see R5 below).
* R3 (locality, **proved**): in every face, any two *ring* vertices have cyclic index distance `<= 2`.
  Proof: the face's Voronoi vertex `x ∈ D` is covered, say `|x−c| ≤ r`, and `x` is nearest to the
  face's cells, so `|x−c_i| ≤ r` for each of them; hence all incident ring disks pairwise intersect at
  `x`, and intersecting ring disks have index distance `<= 2` (locality lemma L1). This holds for
  degenerate faces too (same argument with `k` cells), so refining a face by diagonals between its own
  vertices preserves R3 (the lead's remark, verified).
* R4 (bridge): the hub-hub edge exists (`d = 1`, Part 1).
* R5: ring-only faces are exactly the consecutive triples `(i,i+1,i+2)`: by R3 all three pairs are
  within distance `2`, and the only 3-cliques of `C_9²` are consecutive triples.

**Results.**
* **(A) 8-gon lemma (verified exhaustively).** After a skip-one chord `(i,i+2)`, the side whose boundary
  arc is the long one has the eight ring vertices `0,2,3,...,8` (for `i = 0`) and no hub if both hubs
  are on the other side. A triangulation of that side must use only ring-only faces, i.e. consecutive
  triples. Exhaustive check of all **132 = Catalan(6)** triangulations of the 8-gon: **not one** has all
  faces consecutive (`out/run8_topology_skeleton.txt`). Hence the "long side without hubs" is
  impossible.
* **(A′) Empty ear.** By R4 the two hubs lie on the same side of the chord (the hub-hub edge cannot
  cross it, planarity). They cannot be on the short side (that side would leave the long side without
  hubs, excluded by (A); note the short side's boundary vertices are only `i, i+1, i+2`). So **both hubs
  are on the long side and the short side is exactly the ring-only face `(i,i+1,i+2)`** — every skip-one
  chord cuts out an *empty ear*.
* **(B) `q <= 4`.** An ear `(i,i+1,i+2)` uses the two boundary edges `(i,i+1)`, `(i+1,i+2)` of the dual
  disk; a boundary edge lies in exactly one face, so ears are pairwise **edge-disjoint**: they are
  non-overlapping dominoes on the 9-cycle. Exhaustive count of edge-disjoint ear sets:
  `1 + 9 + 27 + 30 + 9` for sizes `0..4`, none of size `5` — so **`q <= 4`**.
* **(C) Counts.** Degree sum in the dual: `42 = 2E = 18 (boundary) + 2c (chords) + (K−2d) + K` with
  `K = k_1+k_2`, `c = #`skip-one chords, giving **`c + K = 12 + d`**, and with `d = 1`:
  `c + K = 13`. Combined with `q = 11 − K + 2d = 13 − K` (lead's count, re-verified) this gives
  **`q = c`** and `K = 13 − q ∈ {9,...,13}`, `q ∈ {0,1,2,3,4}`. The core has `11 − q = K − 2d` faces,
  all of which contain a hub (no ring-only face survives in the core). **The saved configuration lies
  in the class `q = 0` (`K = 13`)** — that is all that is asserted here; the classes `q >= 1` remain to
  be excluded, and no compatibility statement about them is made (earlier wording "q = 0 is the only
  class compatible with `R_stru`" was unproved and is withdrawn).
* **(D) Deleting the ears.** Removing the `q` ears leaves a core whose boundary is the `(9−q)`-gon of
  the remaining ring vertices, with `9−2q` distance-1 edges and `q` chords, plus the two adjacent hubs
  inside — the lead's "`(9−q)` boundary + 2 adjacent hubs" skeleton.

**Explicitly not proved here (do not register as proved).**
1. *Realizability* of the `q >= 1` classes: nothing above constructs a geometric configuration with an
   ear; each class is only combinatorially consistent.
2. *Exclusion* of the `q >= 1` classes. In particular the "triangular hub cell / degree-3 hub" route
   (lead's earlier conjecture) is **not** forced by these counts: `k_1 + k_2 = 13 − q` with each
   `k_j >= 3` leaves e.g. `(5,5)` for `q = 3`, so a degree-3 hub is a geometric, not combinatorial,
   statement. The retracted form of that conjecture (a chord's ear containing a hub) is impossible by
   (A′): the ear has only ring vertices.
3. Non-trivalent (degenerate) configurations are covered for the *rule* R3 by the diagonal remark, but
   the face-count formulas `v = 11`, `e = 21`, `F = 11` assume trivalence; degenerate cases are handled
   by refining (which preserves R3) and then applying the same count to the refinement.

## Reproduction

`py -3 -B -X utf8 research-2026/team-current/flash-structure/tools/run8_topology_skeleton.py`
(exhaustive 8-gon check, ear-set count, count identities) — evidence
`out/run8_topology_skeleton.txt`. Part 1 is analytic and uses C450's certificate as an input.
