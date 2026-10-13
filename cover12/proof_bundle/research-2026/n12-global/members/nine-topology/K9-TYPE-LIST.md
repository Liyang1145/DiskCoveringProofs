# n12 / k9 branch: complete finite type list of the abstract triangulated dual disk

Scope: every radius-r cover of the unit closed disk D by 12 congruent disks with **exactly nine boundary-active
disks** (tangency counts as active), 0 < r <= U = 0.361102963744508672616920293904, **after** the same-arc
inner-root replacement and after merging coincident hub centers. Level: analytic/combinatorial classification
conditional on the input interfaces (I1)-(I6) below; no metric exclusion, no optimality, no n11 constants.
This file is the type list for the metric scout; companion files `K9-DUAL-DISK.md` (construction + reduction
theorem) and `INTERFACE.md`.

Object: `T` = the **abstract triangulated disk** produced by reducing the clipped Voronoi cellulation with a
per-face fan triangulation (Theorem A of `K9-DUAL-DISK.md`): 9 boundary vertices `R_1..R_9` in cyclic order,
`m <= 3` interior hub vertices, `m >= 1`, every face a triangle, every triangle carrying a **witness**: a point
of D within distance `<= r` of its three site-vertices. Consequences (proved in `K9-DUAL-DISK.md`, Theorem B):

* every edge of `T` has an adjacent triangle whose witness is within `r` of both endpoint sites;
* therefore **no edge of T joins two non-adjacent ring sites**, and the only ring-ring edges are the nine
  boundary **spokes** `R_iR_{i+1}`; every triangle contains at least one hub and at most two ring sites (and two
  only when adjacent);
* `V = 9+m`, `E = 15+3m`, `F = 7+2m` (triangles), interior edges `E-9 = 6+3m`, and the nine **outer triangles**
  (one per spoke) are exactly the `(2 rings, 1 hub)` triangles; the remaining `F-9 = 2m-2` triangles are
  `(1 ring, 2 hubs)` or `(0 rings, 3 hubs)`;
* the hub graph `H = T[hubs]` is connected; `H = K_1` (m=1), `K_2` (m=2), `P_3` or `K_3` (m=3).

Degenerate (higher-order cocircular) cellulations are **not** excluded and need no separate treatment: the fan
triangulation copies the original primal witness into every added triangle, so all statements above hold
verbatim. "Trivalent" only ever meant "the original clipped dual was already triangulated"; it is not a
geometric genericity assumption. (For bookkeeping on the *untriangulated* dual, the identities
`F = 13-(n22+n13+2n23)`, `E_int = F+2`, `n22+n12+2n13+2n23+n03 = 4` are recorded in §5.)

## 0. Input interfaces used

- (I1) inner-root representative (lead `INNER-ROOT-REDUCTION.md`): same r, same actual arcs, nine boundary
  centers of norm in `[1-r, sqrt(1-r^2)]`, other site norms `< 1-r`; all sites distinct, in int D.
- (I2) nine essential owned arcs in cyclic order, exactly nine two-site switches, no triple arc overlap
  (lead `NINE-BOUNDARY-OWNERSHIP.md`).
- (I3) inner-root pair bisector separation (`NINE-BOUNDARY-OWNERSHIP.md`): `dist(0,bisector)<sqrt(1-r^2)<1`;
  the two S^1-points of a pair's bisector are `> 2 asin r` apart, so each adjacent pair has exactly one
  nearest-tie on S^1 and the other bisector point lies outside both owned arcs.
- (I4) non-adjacent ring disks disjoint (lead `NINE-RING-NO-CHORDS.md`, `asin(2r)+6 asin r < pi` for r<=U).
- (I5) coverage of D at radius r. Consequence: every cell `V_s` lies in `B(s,r)`; every hub cell is compact in
  int D; the core `B(0,1-2r)` is covered by hub cells only, so `m >= 1`.
- (I6) = Theorem A of `K9-DUAL-DISK.md` (fan-triangulated dual disk with witness copy). Not an extra
  geometric hypothesis.

## 1. Rigid counts and the enumeration principle

For `T` as above, let `q_i` = the cyclic order of the hub neighbours of `R_i`, a **simple path in H** (the
triangles at `R_i` are the outer triangles `F_{i-1}, F_i` plus `|q_i|-1` inner triangles, one per consecutive
pair of `q_i`); let `t_i = |q_i|`, so `#triangles at R_i = t_i+1` and `deg_T(R_i) = t_i+2`. Each `q_i` starts
at the hub `l_{i-1}` of the outer triangle of spoke `i-1` and ends at `l_i`. Every interior edge lies in exactly
2 triangles, so concatenating `q_1,...,q_9` plus (only when `H=K_3`) the 3-step boundary of the `(0,3)` triangle
gives a **closed walk** in `H` that traverses every hub edge exactly twice. With `t_i <= 3` (only m<=3 hubs) the
chain steps have length `1` or `2`, and the possible data are the ones listed in §2. Consequences used in the
classification: `sum_i (t_i - 1) = #(1-ring inner triangles) = #inner triangles - [H=K_3]` (in the `K_3` case the
`(0,3)` triangle consumes the three remaining hub-edge incidences); the runs of equal labels `l_i` are the spoke
blocks; each run has `>= 1` spoke.

## 2. Complete list (m = 1, 2, 3)

Conventions: hubs are named by their role in H (`K_2`: `u,v`; `P_3`: leaves `L,L'`, middle `M`; `K_3`: `A,B,C`).
A block "(x : s)" means `s` consecutive spokes whose outer triangles carry hub `x`; sizes of all blocks on one
9-cycle sum to 9 and are `>= 1`. "Transition ring" = ring vertex between two consecutive blocks; `t`, chain and
#inner triangles at that ring are listed. Two data are **the same type** iff related by a rotation of the ring
index, by the reflection of the configuration (reversal of the cyclic order), and by renaming hubs inside their
role-preserving automorphism group (for `P_3`: `L <-> L'`, `M` fixed).

### m = 1
| id | data | degrees | triangles |
|---|---|---|---|
| M1 | 9 spokes labelled `h` | `deg(R_i)=3`, `deg(h)=9` | 9 HRR; `F=9` |

### m = 2 (`H = K_2`)
| id | data | degrees | triangles |
|---|---|---|---|
| **M2(s1,s2)** | 2 blocks `(u:s1)`, `(v:s2)`, `s1+s2=9` | `deg(u)=s1+2`, `deg(v)=s2+2`; 2 transition rings `t=2`, `deg=4`; 7 other rings `t=1`, `deg=3` | 9 HRR + 2 HHR; `F=11`, `E=21` |

Classes: `{s1,s2} = {1,8},{2,7},{3,6},{4,5}` -> **4**. Both inner triangles are `(R,u,v)` at the two transition
rings, whose chains are `(u,v)` and `(v,u)`. This derivation replaces an earlier, invalid "`n22=0`" argument
(withdrawn, see §4): the *network* has exactly two transitions because `sum_i(t_i-1) = #inner triangles = 2`;
the untriangulated dual may well have 4-cocircular spoke faces, which the fan triangulation absorbs.

### m = 3, `H = K_3`
| id | data | hub degrees | ring degrees | triangles |
|---|---|---|---|---|
| **T3(s_A,s_B,s_C)** | 3 blocks cyclically `(A,B,C)`, sizes `>=1` sum 9; all 3 transitions have 1-step chains | `deg(X)=s_X+3` | 3 rings `t=2`,`deg=4`; 6 rings `t=1`,`deg=3` | 9 HRR + 3 HHR + 1 HHH; `F=13`, `E=24` |
| **T2(s_A,s_B)** | 2 blocks `(A:s_A)`,`(B:s_B)`, `s_A+s_B=9`; transition `A->B`: chain `A,C,B` (`t=3`, 2 inner triangles); transition `B->A`: chain `B,A` (`t=2`, 1 inner triangle); **hub `C` has `k_C=1` ring neighbour (its spoke block is empty), `deg(C)=3`** | `deg(A)=s_A+3`, `deg(B)=s_B+3`, `deg(C)=3` | 1 ring `t=3`,`deg=5`; 1 ring `t=2`,`deg=4`; 7 rings `t=1`,`deg=3` | 9 HRR + 3 HHR + 1 HHH; `F=13`, `E=24` |

Classes: T3 = multisets `{s_A,s_B,s_C}` (`>=1`, sum 9) -> **7**; T2 = unordered pairs `{s_A,s_B}` -> **4**
(`{1,8},{2,7},{3,6},{4,5}`). "Zero block" case: T2 only; a **single** hub may have an empty spoke block, two
cannot (proof in §3). So "3 label transitions" holds for T3 but not for T2, where `tau = 2`.

### m = 3, `H = P_3` (`L - M - L'`)
| id | data | hub degrees | ring degrees | triangles |
|---|---|---|---|---|
| **P4(s1,s2,s3,s4)** | 4 blocks cyclically `(L:s1)`,`(M:s2)`,`(L':s3)`,`(M:s4)`, each `>=1`, sum 9; all 4 transitions 1-step | `deg(L)=s1+2`, `deg(L')=s3+2`, `deg(M)=s2+s4+4` | 4 rings `t=2`,`deg=4`; 5 rings `t=1`,`deg=3` | 9 HRR + 4 HHR; `F=13`, `E=24` |
| **P3(s_L,s_M,s_L')** | 3 blocks cyclically `(L',s_L')`,`(M,s_M)`,`(L,s_L)`, each `>=1`, sum 9; the `L->L'` transition has the 2-step chain `L,M,L'` (`t=3`, 2 inner triangles), the other two are 1-step | `deg(L)=s_L+2`, `deg(L')=s_L'+2`, `deg(M)=s_M+4` | 1 ring `t=3`,`deg=5`; 2 rings `t=2`,`deg=4`; 6 rings `t=1`,`deg=3` | 9 HRR + 4 HHR; `F=13`, `E=24` |
| **P2(s_L,s_L')** | 2 blocks `(L:s_L)`,`(L':s_L')`, `>=1`, sum 9; **both** transitions are 2-step chains (`t=3`, 2 inner triangles each); `M` is adjacent to exactly the two transition rings, `deg(M)=4`, both its spoke blocks are empty | `deg(L)=s_L+2`, `deg(L')=s_L'+2`, `deg(M)=4` | 2 rings `t=3`,`deg=5`; 7 rings `t=1`,`deg=3` | 9 HRR + 4 HHR; `F=13`, `E=24` |

Middle-hub ring blocks: P4: sizes `s2+1, s4+1`; P3: one block of size `s_M+1` plus one singleton; P2: two
singletons. Leaf spoke blocks are never empty (`deg(L)>=3` and exactly one hub neighbour force `k_L>=2`
i.e. `s_L>=1`; same for `L'`).

Class counts (derived, with the equivalence relation stated above; not load-bearing):
P4 = 4-tuples `(s_i>=1, sum 9)` modulo the Klein four group
`{id, (s1,s2,s3,s4)->(s3,s4,s1,s2) [leaf renaming], ->(s1,s4,s3,s2) [reflection], ->(s3,s2,s1,s4)}`:
`(56+0+12+12)/4 = 20`. P3 = triples modulo `(s_L,s_M,s_L')->(s_L',s_M,s_L)`: `(28+4)/2 = 16`.
P2 = **4**; T3 = **7**; T2 = **4**; M2 = **4**; M1 = **1**. Total m=3: 20+16+4+7+4 = **51**.
Degree checks: m=1 `9+27=36=2E`; m=2 `13+29=42=2E`; m=3 all five families: `sum deg(hubs) + sum deg(rings)
= 18+30 = 48 = 2E` (P-family: `17+31`; T-family: `18+30`; each equals 48).

## 3. Two short lemmas used above

* *At most one empty spoke block in the triangle case.* If two hubs had an empty spoke block (`k=1`), all nine
  outer triangles would carry the third hub, so every chain would begin and end at that third hub and no chain
  could traverse either hub edge of the two `k=1` hubs; but in the `K_3` case the closed walk must traverse the
  three hub edges once each (one HH incidence is consumed by the `(0,3)` triangle), contradiction.
* *m=2 has exactly two transitions.* `sum_i(t_i-1) = #inner triangles = 2m-2 = 2`, and a transition is exactly
  a ring vertex with `t_i = 2` (two different labels); a ring vertex with `t_i = 1` has equal incident labels.
  Hence exactly two transitions, i.e. exactly two blocks.

## 4. Withdrawn statement (provenance)

An earlier version of this file claimed `n22 = 0` for m=2 with a degree argument ("all nine spoke faces contain
h1"). That argument is **wrong**: a `(2,1)` spoke face may be labelled by either hub, so `n22=1` does not force
all spokes onto `h1`. The claim is withdrawn; the correct m=2 treatment is §2 (network level, exactly two
transitions and two HHR inner triangles). Four-cocircular spoke faces in m=2 are a normal degeneration of the
untriangulated dual and are absorbed by the fan triangulation; no degree argument may exclude them.

## 5. Remark: bookkeeping on the untriangulated dual (optional, not needed for the type list)

If one works with the dual `G` *before* fan triangulation, faces can be polygons: with `n_{r,h}` the number of
faces with `r` rings (pairwise adjacent, `<= 2`) and `h` hubs (a path in H),

    m=3: n21+n22+n23 = 9, E_RH = 9+n12+n13, E_HH = 2+n03, n22+n12+2n13+2n23+n03 = 4,
         F = 13-(n22+n13+2n23), E_int = F+2 ;
    m=2: n21+n22 = 9, E_RH = 9+n12, E_HH = 1, n22+n12 = 2 (n22 = 0,1,2 all possible in principle:
         n22=0 already triangulated, n22>=1 cocircular spoke faces) ,
         F = 11-n22, E_int = 12-n22 .

Every such `G` fans into one of the §2 networks; the network counts (`F=7+2m`, `E=15+3m`) are rigid and are the
ones a metric certificate should be written against.

## 6. Checks against the lead's bookkeeping

* `F = 13`, `E_int = 15` for m=3: confirmed at the network level (`F=7+2m`, `E=E_int+9=15+3m`), with no
  genericity assumption; the nine outer triangles are HRR and the 4 inner ones are HHR/HHH.
* `K_3`: `9 HRR + 3 HHR + 1 HHH` for **both** T3 and T2; `tau = 3` for T3, `tau = 2` for T2 (one hub of degree
  3, single empty block). Two empty blocks are impossible (§3).
* `P_3`: `9 HRR + 4 HHR` for all of P4 (tau=4), P3 (tau=3), P2 (tau=2, middle hub degree 4, both middle blocks
  empty). Leaf blocks never empty.
* `m=2`: network `F=11 = 9 HRR + 2 HHR`, `E=15+3m=21`; 4 classes up to hub renaming.
* Corrections to this member's earlier drafts: the m=2 `n22=0` claim is withdrawn (§4); the P4 orbit count 34
  was an overcount — with the equivalence group of order 4 stated at §2 the count is 20 (`(56+0+12+12)/4`).
  All type counts are bookkeeping under the stated equivalence, not a load-bearing claim.
* Fan triangulation + witness copy is the correct device for degenerate cocircular cellulations: it makes the
  counts rigid and keeps "all edges <= r" (each added triangle reuses the primal witness of its face); the
  earlier attempt to exclude degeneracies combinatorially was unnecessary and is not used anywhere.
