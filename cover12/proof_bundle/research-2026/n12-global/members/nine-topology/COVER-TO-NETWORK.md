# Covers at r <= U with k=9 to one of the 56 witness networks + 9 anchor gaps <= L

Scope-clarifying implication proof, written by the producer of `K9-DUAL-DISK.md` / `K9-TYPE-LIST.md` /
`graphs.json`. Purpose: state exactly which premises are already proved, in which file, and which are *not*.
No new claim, no new numerical work, no review chain. This file proves nothing about metric exclusion; the
per-type metric certificates are the lead's (`NETWORK-TAYLOR-CERTIFICATE.md`, `network-certified-*.json`).

## 1. Statement of the implication

Hypothesis H: twelve congruent closed disks of radius r cover the unit closed disk D, `0 < r <= U
= 0.361102963744508672616920293904`, and exactly nine of them meet `S^1 = dD` (tangency counts as meeting).
Conclusion: there exist `m in {1,2,3}`, a witness network `T` from the catalogue `graphs.json` (M1, M2, P4,
P3, P2, T2; T3 included for completeness), with the standard indexing (rings 0..8, hubs 9..8+m, anchor i
between ring i and ring `i+1 mod 9`), and nine positive angles `Delta_0..Delta_8` with

    sum_i Delta_i = 2*pi ,   0 < Delta_i <= L := 2*asin(U) ,   and `(T, Delta)` is the reduced graph of the cover.

The pair `(T, Delta)` is what the lead's certificate consumes (full 9-gap simplex with the cap L, plus the
graph).

## 2. Inputs, with provenance and status

| id | statement needed | where proved | status |
|---|---|---|---|
| (a) | same-arc inner-root replacement: coverage and the nine actual arcs are preserved, and the representative has ring-center norms in `[1-r, sqrt(1-r^2)]`, other distinct centers of norm `< 1-r` | `lead/INNER-ROOT-REDUCTION.md` (analytic; scope: all covers, `0<r<1`) | proved |
| (b) | eight arcs cannot cover `S^1` (`8*2 asin r < 2 pi`), so the nine actual arcs are essential; none contains another and the circular (midpoint) order is strict; at most two actual arcs meet at any point | `lead/NINE-BOUNDARY-OWNERSHIP.md` sections "Essential arcs and circular order" | proved |
| (c) | non-adjacent ring disks are disjoint; equivalently the actual arcs of non-adjacent rings are disjoint | `lead/NINE-RING-NO-CHORDS.md` (C933; uses (b) and `asin(2r)+6 asin r < pi` for `r<=U`, rational form `< 1529/500 < pi`) | proved |
| (d) | inner-root pair tie lemma: for two ring sites of norm `<= sqrt(1-r^2)` the bisector line satisfies `dist(0,bisector) < sqrt(1-r^2) < 1` and its two `S^1` points are `> 2 asin r >=` arc length apart, so at most one nearest-tie of the pair lies in either arc | `lead/NINE-BOUNDARY-OWNERSHIP.md` section "A same-radius inner-root pair has at most one tie in any actual arc"; re-derived in `K9-DUAL-DISK.md` Lemmas 1.3/1.4 | proved |
| (e) | nearest-owned boundary arcs are nondegenerate intervals, one per ring, separated by exactly nine two-site switches | `lead/NINE-BOUNDARY-OWNERSHIP.md` section "Nearest ownership" **combined with (c)**: on the actual arc `A_i` the only possible competitors are `c_{i-1}, c_{i+1}` (non-neighbours have disjoint arcs by (c), hubs are `> r` away on `S^1`), and by (d) each competitor ties `c_i` in at most one point, so the owned set of `i` is one interval whose two ends are the ties with `i-1` and `i+1` | proved using (c); the flagged order step of that file ("only cyclic neighbours overlap ... should receive an independent combinatorial check") is **not used** (see §4.1) |
| (f) | coverage of D at radius r | branch hypothesis H | hypothesis, not proved |
| (g) | exactly nine boundary-active disks, twelve disks in total | branch hypothesis H | hypothesis, not proved |

Direct answer to "are the premises all already in `NINE-BOUNDARY-OWNERSHIP.md` and C933?": **no, not all, and
one of them is deliberately not used in the form stated there.**
* `NINE-BOUNDARY-OWNERSHIP.md` supplies (b) and (d) (both proved there), and states (e); C933 supplies (c).
* (e) as stated in that file uses the "only cyclic neighbours overlap" order step which that file itself marks
  as requiring an independent check. Here (e) is instead *derived* from (b)+(c)+(d) (step 3 plus the paragraph
  in the table), so the flagged step is bypassed entirely; nothing downstream in this chain uses it.
* Positive facets, the degree-3 switch structure and the outer-cycle topology are not quoted from those files:
  they are proved in `K9-DUAL-DISK.md` (Lemma 1.3, Lemma 1.4, section 2), using (b),(c),(d) plus the secant
  bisector computation of (d).
* "Delete duplicate hubs, keep positive cells" is not in either file: cells satisfy `s in int V_s` and
  non-adjacent rings have disjoint cells by (c) (Lemma 1.1/1.2 of `K9-DUAL-DISK.md`), so merging coincident
  non-boundary centers keeps every remaining cell positive; two boundary centers cannot coincide by (b).
* (f) and (g) are the branch hypotheses and are *not* proved anywhere; they are exactly the input H.

## 3. The implication, step by step

1. **Reduce to distinct sites.** Apply (a). Two of the nine boundary-active centers cannot coincide: they would
   have the same actual arc, contradicting essentiality (b); a "hub" coinciding with a ring center would itself
   be boundary-active, giving ten boundary-active disks, contrary to H. So the only possible coincidences are
   among the other distinct centers; merge them. Write `m` for the number of distinct non-boundary centers,
   `m = 12 - 9` at most, so `m <= 3`.
   *Deleting duplicates keeps positive cells*: for every remaining site `s`, `s` minimises its own distance
   strictly, so `s in int V_s`; cells are convex with nonempty interior. No non-removability of hubs is used
   anywhere (a redundant hub still has a positive cell and remains a dual vertex).
2. **Cellulation and the coverage bound.** By (f), every clipped cell satisfies `V_s subset B(s,r)`; hence by
   (c) non-adjacent ring cells are disjoint. The open core `B(0,1-2r)` is nonempty (`r <= U < 1/2`) and contains
   no point of any ring disk (ring norms `>= 1-r`), so it is covered by hub cells: `m >= 1`. `K9-DUAL-DISK.md`
   Lemma 1.2.
3. **Switches and spokes.** Each switch `u = w_i` from (e) has exactly `c_i,c_{i+1}` nearest and equal with
   common distance `rho <= r`; every other site is strictly farther: non-neighbour rings do not cover `u` (their
   arcs are disjoint from `A_i` by (c)), the third ring `c_{i-1}` may not be within distance `rho` either
   (otherwise `u` would lie in three actual arcs, contra (b)), and hubs satisfy `|u-h| > r >= rho`. The pair's
   bisector is secant by (d); starting from `u` along its inward ray, all strict inequalities persist by
   continuity (1-Lipschitz distance functions), so an interval of positive length of the bisector lies in
   `V_{c_i} cap V_{c_{i+1}}`. Hence: exactly nine boundary vertices, each of degree 3 (two boundary arcs + one
   interior **spoke**), each spoke of positive length. `K9-DUAL-DISK.md` Lemma 1.3.
4. **Ring-ring facets are exactly the spokes.** If an interior primal vertex lies in `V_{c_i} cap V_{c_j}`
   (`i != j`), then the pair is adjacent, the point is the inner endpoint of their spoke and the two cells are
   consecutive there; hence the only 2-ring face of the dual is that spoke face. At any interior primal vertex
   at most two ring cells meet and then they are adjacent (otherwise their disks would both contain the vertex,
   contradicting (c)); every interior primal vertex therefore touches at least one hub.
   `K9-DUAL-DISK.md` Lemmas 1.4, 1.5.
5. **Dual disk and outer cycle.** Build `G` (nodes = cells, edges = positive-length facets). Its bounded faces
   are the interior primal vertices; dualising the cellulation compactified by the exterior face (each switch
   face is a triangle by step 3) shows that the outer face of `G` is the simple cycle
   `R_0 R_1 ... R_8`. Euler: `V = 9+m`, `E = 9 + E_RH + E_HH`, bounded faces `v = 1 + E_RH + E_HH - m`.
   Counting ring-face incidences (nine spoke faces contribute two rings each) gives `E_RH = 9 + n1` and hence
   `E_HH = m - 1 + n03 >= m - 1`, so the hub graph is connected and `H in {K_1, K_2, P_3, K_3}`.
   `K9-DUAL-DISK.md` section 2 and Corollary 2.1.
6. **Abstract triangulation, all degeneracies covered.** Fan-triangulate every (convex) face of `G` and give
   each new triangle the witness of its face (a primal vertex within `r` of every incident site). This yields an
   abstract triangulated disk `T` with 9 boundary rings, `m` hubs, `F = 7+2m`, `E = 15+3m`, nine boundary
   spokes, and: no edge joins non-adjacent rings, no triangle has three rings, every triangle has a hub.
   `K9-DUAL-DISK.md` Theorem A, Theorem B, Corollary C.
7. **Enumeration.** Each hub edge lies in exactly two triangles; a 1-ring triangle per chain step; a `(0,3)`
   triangle only in the `K_3` case. Hence the closed-walk classification with step multisets
   `{1,1,1,1},{2,1,1},{2,2}` (`P_3`), `{1,1,1},{2,1}` (`K_3`), `{1,1}` (`K_2`), `{}` (`K_1`), i.e. exactly the
   families M1, M2, P4, P3, P2, T2, T3 of `K9-TYPE-LIST.md` section 2; `graphs.json` lists one entry per
   isomorphism class, generated and integer-checked by `gen_graphs.py` (F, E, boundary = 9,
   interior = 6+3m, faces by type, no non-spoke RR edge, ring/hub degrees, hub connectivity, Euler).
8. **The nine anchor gaps.** The owned boundary arcs of the rings are the open intervals between consecutive
   switches (step 3 + (e)); their angular widths `Delta_i > 0` satisfy `sum Delta_i = 2 pi` (they partition
   `S^1` up to the nine switches) and `Delta_i <= width(A_i) <= L = 2 asin U`: the owned arc is contained in
   the actual arc, and the actual arc has halfwidth `alpha <= asin r`, because with the inner-root norm bound
   `|c_i| <= sqrt(1-r^2)` one has `cos alpha = (1+|c_i|^2-r^2)/(2|c_i|) >= sqrt(1-r^2) = cos(asin r)` (as in
   (a); `cos` decreasing on `[0,pi]`). Anchor `i` (the spoke between ring `i` and ring `i+1`) is the switch
   between `Delta_i` and `Delta_{i+1}`; the pairing of anchors with rings is the cyclic order supplied by
   (b)+(e), matching the indexing of `graphs.json`.

## 4. Explicitly not proved here / not to be treated as proved

1. **The flagged order step** of `NINE-BOUNDARY-OWNERSHIP.md` ("only cyclic neighbours overlap ... should
   receive an independent combinatorial check") is neither proved nor used in this chain: what is used is the
   stronger, independently proved non-neighbour disjointness (c). Any downstream use of "only neighbours
   overlap" as such must supply its own check.
2. The nine-switch structure (e) is *derived* here from (b)+(c)+(d) and is not an extra hypothesis; but it is
   derived, not quoted, so the derivation in step 3/§2(e) is the load-bearing text.
3. No metric statement: this file gives no exclusion of any of the 56 types and no bound on `r_D(12)`. The
   per-type certificates for the lead's candidate/non-candidate work are external inputs (lead's files).
4. Realizability of arbitrary parameter tuples of a family by an actual cover is not claimed; the list is a set
   of necessary conditions.
5. The inner-root replacement is applied *before* the graph is extracted, so switch positions, spoke lengths,
   the four-cell (cocircular) combinatorics and any contact pattern of the original cover are **not**
   preserved; only the existence of some representative with the stated network is claimed.
6. Hubs are not assumed non-removable, non-coincident, or strictly interior to any particular cell; the branch
   hypotheses (f),(g) are the only assumptions about the cover.
7. The classification assumes the `r <= U` regime through (b) (`8 asin r < pi`, true at `r <= U < sin(pi/8)`)
   and (c) (`asin(2r)+6 asin r < pi`); outside `r <= U` the same proof does **not** apply.

## 5. Interface to the metric certificate

Certificate input produced by this chain: one graph `T` from `graphs.json` (`faces` list, rings 0..8, hubs
9..8+m, anchors between consecutive rings) and the nine gaps `Delta_i in (0, L]`, `sum Delta_i = 2 pi`, i.e. a
point of the full 9-gap simplex with the cap `L = 2 asin U`, exactly the domain used in
`lead/NETWORK-TAYLOR-CERTIFICATE.md` (`theta_i = i L - D sum_{j<i} y_j`, `D = 9L - 2 pi`). The reduction
therefore supplies precisely: *for every cover satisfying H, some graph of the catalogue together with some
point of the capped simplex*. It does not and cannot supply which one; the certificates must cover all
catalogue entries, which is why the catalogue is enumerated completely (56 entries).
