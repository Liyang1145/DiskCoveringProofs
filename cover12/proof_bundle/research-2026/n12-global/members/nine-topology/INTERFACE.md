# n12 / k9 branch — central reduction interface ledger

Read alongside `K9-DUAL-DISK.md` (proofs) and `K9-TYPE-LIST.md` (type list). This file states only interfaces:
what is imported, what is exported, at which scope, and what remains open. No truth certification.

## A. Imports (each used with the scope it is proved at)

| id | statement | scope | source |
|---|---|---|---|
| I1 | same-arc inner-root replacement; representative with nine boundary centers of norm in `[1-r,sqrt(1-r^2)]`, other centers `< 1-r`, actual arcs and coverage preserved, old switches not preserved | global, all covers at `0<r<1` | lead `INNER-ROOT-REDUCTION.md` (analytic) |
| I2 | nine essential owned arcs, cyclic order, no triple arc overlap, exactly nine two-site switches | k=9 branch at `r<=U` | lead `NINE-BOUNDARY-OWNERSHIP.md` (one order step flagged for independent check; not used here in that form) |
| I3 | inner-root pair bisector separation: `dist(0,bisector)<=sqrt(1-r^2)<1`; each adjacent pair has exactly one nearest-tie on S^1, other bisector point outside both arcs | k=9 branch | `NINE-BOUNDARY-OWNERSHIP.md`; re-derived in `K9-DUAL-DISK.md` Lemma 1.3/1.4 |
| I4 | non-adjacent ring disks disjoint, via `asin(2r)+6 asin r < pi` for `r<=U` | k=9 branch | lead `NINE-RING-NO-CHORDS.md` (rational verification; independently reviewed by finite-reduction member) |
| I5 | coverage of D at radius r (branch hypothesis); gives `V_s subset B(s,r)` and core `B(0,1-2r)` covered by hubs | k=9 branch | standing hypothesis |

## B. Exports (proved in `K9-DUAL-DISK.md`, conditional on A)

Integrated form of E1-E5 (single statement for downstream use): *for every radius-r cover of D by 12 congruent
disks with exactly nine boundary-active disks and `r <= U`, after inner-root replacement and merging hub
duplicates, the distinct sites are nine rings and `m in {1,2,3}` hubs, and the cover admits an abstract
triangulated disk `T` with 9 boundary ring vertices, `m` hub vertices, `F = 7+2m` triangular faces
(`13, 11, 9` for `m = 3,2,1`), `E = 15+3m`, nine boundary spokes, a common witness within `r` for every edge,
connected hub graph `H in {K_1, K_2, P_3, K_3}`, and the complete type list of `K9-TYPE-LIST.md` §2 (m=3:
`P4, P3, P2, T3, T2`; the zero-block types `T2, P3, P2` included).* No genericity assumption is used; the
triangulation is artificial and its witnesses are the original primal vertices.

| id | statement | level | consumers |
|---|---|---|---|
| E1 | cells honest (convex, nonempty interior, tile D, adjacency connected); hubs compact in int D, `m>=1`, `m<=3` | analytic, global in branch | any k9 use |
| E2 | switches are the only boundary vertices, each degree 3, one positive-length spoke; the only ring-ring facets are the nine spokes; each spoke face is the only 2-ring face | analytic, global in branch | arc/ownership consumers |
| E3 | abstract triangulated dual disk `T` with witness copy (fan-triangulate every face, copy the primal witness); `F = 7+2m`, `E = 15+3m`, 9 spokes, all faces triangles | analytic, global in branch, **no genericity assumption** | metric certificates |
| E4 | in `T`: no edge joins non-adjacent rings, no triangle has 3 rings, every triangle has `>=1` hub, hub graph `H` connected, `H in {K_1,K_2,P_3,K_3}` | analytic, global in branch | type-based metric work |
| E5 | each hub edge lies in exactly 2 triangles (one of them the `(0,3)` triangle in the `K_3` case), which yields the closed-walk classification: m=3 families `T3,T2,P4,P3,P2`; m=2 `M2`; m=1 `M1`, including all zero-block faces | analytic + finite enumeration | metric scout (per-type certificates) |
| E6 | straight-site realization: nodes at sites, straight edges for facet-sharing pairs, non-crossing, faces convex; `B(0,1-r) subset conv(ring sites)` so hubs lie inside | analytic | metric parametrization |

## C. What the metric scout can rely on

* Rigid counts: `F = 7+2m`, `E = 15+3m`, interior edges `6+3m`; at m=3: 9 outer (2R,1H) triangles + 4 inner
  (1R,2H)/(0R,3H) triangles. These are independent of cocircular/degenerate cell structure, because the fan
  triangulation absorbs it.
* Per-type data: block structure (labels + sizes), transitions and chains, hub degrees
  `deg(h) = k_h + q_h`, ring degrees `deg_T(R_i) = t_i + 2`, and the nine outer triangles. Tables in
  `K9-TYPE-LIST.md` §2.
* Locality of artificial edges: every edge of `T` (real or artificial) has a common witness in D within
  distance `r` of both endpoint sites. So any argument of the form "an edge whose endpoints are two ring sites
  must be a spoke" applies to artificial edges too, with no extra hypothesis.
* Type list is complete as a list of *necessary* conditions: every k9 cover at `r<=U` produces one of the
  families with some parameter tuple. Realizability of every parameter tuple by a covering is NOT claimed
  (the scout's metric work decides that); conversely the list should not be assumed realizable for arbitrary
  tuples.
* Counts of types (M1 1; M2 4; P2 4; P3 16; P4 20; T2 4; T3 7) are orbit counts under the equivalence stated
  in `K9-TYPE-LIST.md` §2 (rotation, reflection, hub renaming). They are bookkeeping, not a load-bearing claim.

## D. Explicit non-claims and open obligations

1. No metric exclusion of any family; no lower bound for `r_D(12)`; the k=10 and k=11 branches are untouched.
2. Untriangulated degenerate cell structures need no separate enumeration for the *interface* (E3), but metric
   work written against the untriangulated dual must use the identities of `K9-TYPE-LIST.md` §5
   (`F = 13-(n22+n13+2n23)`, `E_int = F+2`, `n22+n12+2n13+2n23+n03 = 4`) or first fan-triangulate.
3. Corrections inside this member's own earlier drafts (kept for provenance): the m=2 claim `n22 = 0` is
   withdrawn (wrong degree argument; see `K9-TYPE-LIST.md` §4); the P4 orbit count 34 was an overcount
   (correct group of order 4, count 20); "trivalent" is not a geometric genericity assumption, only
   "the untriangulated dual was already triangulated".
4. Next executable obligations: (a) per-family metric exclusion or candidate certification for k9 at `r<=U`;
   (b) k=10/k=11 branch handling; (c) if a family's parameter simplex needs a lower-dimensional face
   (some size `= 0`), note that T2/P2/P3 are exactly the zero-block faces and are included above.

## E. Provenance / independence notes

* This member did not transplant any n11 classification, constant or certificate; the only numeric input is the
  n12 inequality I4 and `r <= U < 1/2`.
* The hub-connectivity result E4 is proved twice independently here: by the counting identity
  `E_HH = m-1+n03 >= m-1` (with the `m<=3` graph observation) and by the bounded-face label argument
  (both in `K9-DUAL-DISK.md` §2). The lead's face-adjacency short proof was checked step by step; its
  "bounded-face adjacency is connected" step is justified by the local chaining of faces at every node.
* The straight-site realization E6 is the standard lifted-Delaunay duality, plus the elementary convexity fact
  `B(0,1-r) subset conv(ring sites)`; no perturbative genericity is used.
