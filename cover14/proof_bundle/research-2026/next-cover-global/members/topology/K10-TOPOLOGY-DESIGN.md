# n14, k=10 branch: conditional dual-disk topology — design + executed enumeration

New product of `research-2026/next-cover-global/members/topology/`. Conditional on the inputs (K1)-(K4)
below; none of them is re-proved or re-audited here. No numerical proof (integer combinatorics only).
n11/n12 assets read-only as blueprints; nothing transplanted.

Files: `gen_k10_catalogue.py` (integer enumerator), `k-catalogue-calib.json` (n12 calibration),
`k-catalogue-n14.json` (this catalogue).

## 0. Conditional inputs

| id | statement | source / status |
|---|---|---|
| (K1) | k=10 boundary ownership: ten connected nearest-owned boundary arcs, ten two-site switches | `lead/BOUNDARY-OWNERSHIP-PROOF.md` (new, lead's independent proof: bisector's two circle-intersection points are `> 2 asin r` apart while an actual arc has length `<= 2 asin r`, plus the private interval, excluding degenerate endpoint sets). **The structure member's earlier draft (convex-cell radial cone) was rejected and is not used.** |
| (K2) | **no chords**: non-adjacent ring *disks* are disjoint. This is *stronger* than "non-adjacent ring cells are disjoint" and the two are **not equivalent**; only the implication disks-disjoint ⇒ cells-disjoint (via coverage `V_s subset B(s,r)`) is used | structure member; the main measure argument was reviewed as valid by the lead, canonical `r <= U`, reusing the same-arc inner-root replacement |
| (K3) | C1142: for `r <= U = 0.33173203427623414 < 1/3` the projected active count is `k in {10,11}` | lead's proved claim (assumed) |
| (K4) | coverage of D by 14 congruent radius-r disks | branch hypothesis |

**m after merging duplicate hubs.** `m = #distinct non-boundary centers in {3,4}`:
`<= 4` because `14 - k <= 4`; and `m >= 3` by the core count: the core `B(0,1-2r)` is covered by hub cells only
(ring sites have norm `>= 1-r`, so `|x-c_i| > r` on the core), hence its boundary circle (radius `1-2r > r`)
is covered by the `m` distinct hub disks; each such disk cuts that circle in an arc of halfwidth
`asin(r/(1-2r)) < pi/2` (as `r < 1-2r`, i.e. `r < 1/3`), so two disks cover `< 2 pi` of it and at least three are
needed. **Branch bookkeeping (corrected):** the number of rings equals the number of boundary-active disks, so
the k=11 branch has `N=11` rings and `m=3` exactly (three hub disks, no merging possible), while the k=10 branch
has `N=10` rings with `m in {3,4}` (four hub disks, two of which may coincide). The `N=10, m=3` catalogue is
therefore k=10 with a merged hub pair and does **not** cover k=11; k=11 needs its own `N=11, m=3` catalogue
(generated below, 85 entries).

## 1. Structure and counts — stated on the fan-triangulated network `T`

Same-arc inner-root replacement (read-only) puts all sites in int D with ring norms in
`[1-r, sqrt(1-r^2)]`, hub norms `< 1-r`; merging coincident hubs keeps positive cells.
Under (K1)+(K2)+(K4) the n12-style structural lemmas go through with the ring count `N` as the only change:
coverage bound `V_s subset B(s,r)`; non-adjacent ring cells disjoint; the only ring-ring facets are the `N`
spokes; at each interior primal vertex at most two ring cells meet, and then they are adjacent — hence
**every face of the dual `G` contains at least one hub**, and the outer face of `G` is the `N`-spoke cycle
`R_0..R_{N-1}`; the hub graph `H` is connected (face-adjacency label argument).

**Counting is done only on `T`** (fan-triangulate every face of `G` first), because untriangulated faces may be
polygons and their ring/hub incidence must not be pushed through Euler before triangulation. With
`V = 10+m` and all faces triangles:

    F = 8 + 2m ,  E = 17 + 3m ,  interior edges = 7 + 3m ,  outer triangles = 10 ,
    inner triangles = 2m - 2 = #(1R,2H) + #(0R,3H) ,   #(0R,3H) = H3 = E_HH - m + 1 ,

the last identity because each hub edge lies in exactly two triangles: `3 H3 + #(1R,2H) = 2 E_HH`, subtract
`H3 + #(1R,2H) = 2m-2`. (Consistency remark, not used: the same number equals the number of 0-ring faces of the
untriangulated `G`; consequently every 0-ring `G`-face is a triangle, since a `h`-hub 0-ring face would fan into
`h-2` triangles and `sum (h_f - 2) = H3` forces `h_f = 3`.)

**Degeneracies and the fan convention.** A face of `G` may be a `k`-gon (higher-order cocircularity); it is
fanned and every added triangle inherits the face's primal witness, which lies within `r` of all incident sites.
Choose the fan vertex to be a **hub** (every face has one): then every added diagonal is hub-to-site, so **no
artificial ring-ring edge (ring chord) is ever introduced**, and a 2-ring face is the spoke face whose ring pair
is already adjacent. Collinearity is harmless (a pair's common facet is convex and lies on one line).

**Disk criterion used by the checks** (explained, no orientation bookkeeping): verify that each edge lies in
`<=2` triangles, the ten spokes in exactly 1 and all other edges in exactly 2; that the link of every hub is a
single cycle and the link of every ring is a path from `i-1` to `i+1`; that the complex is connected; then it is
a compact connected triangulated surface with boundary, and the 1-triangle edges form a single boundary cycle
(the ten spokes), so `chi = V - E + F = 1` — by the classification of surfaces that is a triangulated disk.
The rotation system is determined by these data, so no extra orientation input is needed.

## 2. Hub graphs (answer: K4 allowed; C4 excluded)

`H` is connected on `m` vertices, `m in {3,4}`. Planarity excludes nothing (all connected graphs on `<= 4`
vertices are planar), so **`K_4` is not excluded a priori** — but `H3 = E_HH - m + 1` is forced, and `H3` must be
a set of `H3` triangles of `H`:

| m | `H` | `E_HH` | forced `H3` | hub-only triangles | `S = sum_e (2-t_e) = 2m-2-H3` |
|---|---|---|---|---|---|
| 3 | `P_3` | 2 | 0 | – | 4 |
| 3 | `K_3` | 3 | 1 | the unique triangle | 3 |
| 4 | `P_4` | 3 | 0 | – | 6 |
| 4 | `K_{1,3}` | 3 | 0 | – | 6 |
| 4 | `C_4` | 4 | 1 | **excluded: `C_4` has no triangle** | – |
| 4 | `K_3 + pendant` | 4 | 1 | the `K_3` | 5 |
| 4 | diamond `K_4-e` | 5 | 2 | both triangles (share the diagonal) | 4 |
| 4 | `K_4` | 6 | 3 | 3 of its 4 triples (4 skeletons) | 3 |

## 3. Enumeration interface and executed results

Data per skeleton: a closed walk in `H` using each hub edge `e` exactly `c_e = 2 - t_e` times, cut into 10
consecutive blocks assigned to rings `0..9` in cyclic order (empty blocks allowed). Blocks are the ring chains
`q_i` (simple paths from `l_{i-1}` to `l_i`); the labels `l_i` **are determined** by the walk and the cut, so no
separate search over `10^m` labelings is needed. Triangles: outer `(i, i+1, 10+l_i)`, inner `(i, h, h')` per
consecutive chain pair, hub-only from the skeleton. Then the checks of §1, then canonicalisation under ring
rotation (10), reflection (2) and hub renaming (`Aut`; `m!` used) and dedup.

**Calibration (n12, N=9, m<=3):** the same generator reproduces the known n12 catalogue: `m=1: 1`, `m=2: 4`,
`m=3: 51` → **56** entries (`k-catalogue-calib.json`). Equal counts were not accepted as evidence: `join56.py`
performs a **complete isomorphism join** against the old n12 `graphs.json` (canonical forms under ring
rotation, reflection and hub relabeling) and returns a perfect **56 ↔ 56 bijection with no unmatched key**.

**n14 run (N=10, executed):**

| m | skeletons (attempts) | valid after checks | phase-1 keys | catalogue | time |
|---|---|---|---|---|---|
| 3 | P3 (2860), K3 (1320) — 4,180 attempts | 2,910 | 291 | **93** | 0.6 s |
| 4 | P4 (30030), K13 (60060), K3P (20020), diamond (5720), K4 (4×1320) — 121,110 attempts | 52,590 | 5,259 | **1,442** | 26.2 s |
| total | 125,290 attempts | 55,500 | 5,550 | **1,535** | 27 s wall |

Per-skeleton catalogue shares (m=4): P4 566, K3P 509, K13 223, diamond 125, **K4 19**; `C_4` contributes 0
(no hub-only triangle available). m=3 (N=10): P3-derived 74, K3-derived 19. All 1,535 stored entries were
re-checked from scratch afterwards (Euler `V-E+F=1`, `(V,E,F)=(10+m,17+3m,8+2m)`, spoke edges in 1 triangle and
all others in 2): all pass. Output: `k-catalogue-n14.json`. Runtime is reported as measured, not promised.

**n14 k=11 branch (N=11, executed):** 4,070 attempts → **85** entries (0.9 s), file `k-catalogue-k11.json`.
This is a *different* family from the N=10, m=3 list (11 rings vs 10) and the two must not be conflated.

**Bridge.** `COVER-TO-DUAL.md` proves the cover → *topological* dual disk interface needed by the certificate:
curved dual (site-to-facet-midpoint spokes), bounded faces = Voronoi-vertex stars on empty balls (convex
position, hence fannable, common witness `x` with `|x-s| <= r`), outer boundary = ring cycle via the
radial-arc collar. No straight-line realisation and no hull-outer-layer assumption is used or needed.

## 4. Forced / eliminable parameters

`H3 = E_HH-m+1`, `#(1R,2H) = 2m-2-H3`, `t_e`, `c_e = 2-t_e`, `S = 2m-2-H3` are forced by the skeleton;
the labels are derived from `(walk, cut)`; ring degrees `deg_T(R_i) = t_i+2` with `t_i = 1 + |block_i|`;
the number of transition rings = number of nonempty blocks. Free combinatorial data: the walk/cut choice
(125,290 attempts total) and the symmetry quotient. For the metric certificate the scout needs the triangle list
plus the `N` anchor gaps `Delta_i in (0,L]`, `sum Delta_i = 2 pi`, `L = 2 asin U` — the anchored simplex as in
the n12 interface.

## 5. Status ledger

* **Executed and verified:** calibration (56, with a complete 56↔56 isomorphism join) and the n14 catalogues
  (k=10: 93 + 1442 = 1535; k=11: 85) with the integer checks of §1/§3; `C_4` excluded by construction;
  `K_4` included with 19 entries; the cover→topological-dual bridge is proved in `COVER-TO-DUAL.md`.
* **Assumed (not proved here):** (K1) `lead/BOUNDARY-OWNERSHIP-PROOF.md`; (K2) structure member's no-chord
  argument (lead-reviewed); (K3) C1142; (K4) coverage.
* **Explicitly still unproved (must not be presented as proved):** (i) realizability of catalogue entries by
  actual covers (the catalogue is necessary conditions only); (ii) every metric exclusion (in particular no
  k=10/11 stress or Taylor certificate is claimed here); (iii) the n14 optimum or any lower bound.
  The straight-line realisation is deliberately *not* claimed and *not* needed: the certificate consumes the
  incidence plus the common witnesses of `COVER-TO-DUAL.md` only.
  (iv) the n14 optimum or any lower bound.
* **Next executable step:** hand `k-catalogue-n14.json` (1535 entries, rings 0..9, hubs 10..) to the metric
  scout; the m=3 list serves both the k=11 branch and the k=10 branch with merged duplicate hubs.
