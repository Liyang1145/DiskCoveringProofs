# Strict-hub feasibility = finite min-norm candidates; and the strict Helly ≤3-witness disjunction

Author: r20-geometry (cline2 route, no subagents). Write scope: this directory only; `lead/` untouched;
**no claim registered**; **no grids, no sampling, no optimisation** in any statement below (the only
computation is the closed-form finite candidate evaluation of §6, evidence
`strict_hub_finite_disjunction.py/.out.txt/.json`).

**Chinese scope line (口径行).** 对象：任意合法邻接 ring chain（C879 假设：每边唯一公共覆盖等距点），
半径 `r∈(0,1)`，`ρ=1−r`，strict hub `|h|<ρ`。结果：①严格 hub 存在 ⟺ 有限候选集上的 min-norm 判据
（Theorem A，无 CQ、无 Slater、无生成性假设）；②不存在严格 hub ⟺ `{B(0,ρ)}∪{B̄(p_j,r)}` 中某个
**≤3 元子族**空（Theorem B，Helly，开球 ⟹ 半径盘侧用 `≥`、纯盘三元用 `>`）；③闭交 singleton/empty
时 CQ/Slater 失效，KKT/乘子形式不可用，但 A/B 仍可判；④两者都是 ring-only 的有限析取（每条边只通过
内交点 `p_j=p_j(c_i,c_j,r)` 进入）。对象实例：q0(6,7) 9-ring inward root，两个 fan（m=4,5），
strict hub 均存在（margin 0.347 / 0.471）；fan B 的闭交在对象精度内就是 singleton `{hub}`（无 Slater），
判据仍给出正确答案。central coupling（两 hub 之间的两条中央三角形约束）**仍缺**，本件不做。

---

## 0. Correction of the closed-domain classification of my previous note (degenerate extra at y=0)

For one edge, local frame `a=(−d/2,0)`, `b=(d/2,0)` (ring centres), `p_in=(0,−k)`, `p_out=(0,+k)`,
`k=√(r²−d²/4)`, `y` the coordinate along the radical direction, `F_in=|h−p_in|²−r²`,
`F_out=|h−p_out|²−r²`, `R_c` = circumradius of `(a,b,h)`, and the identity

$$4y^2(R_c^2-r^2)=F_{in}F_{out},\qquad F_{in}-F_{out}=4ky .$$

The argument "`F_in≤0 ⟹ F_inF_out≤0 ⟹ R_c≤r`" used in §2/A5 of
`AUDIT-CLOSED-H-AND-STRICT-HUB.md` ("no extras on the closed domain") **silently divides by
`4y²`**. The correct statement is:

> `F_in ≤ 0` and `y ≠ 0` ⟹ `R_c ≤ r` (**no extras off the base line**);
> `F_in ≤ 0` and `y = 0` ⟹ `F_in = F_out = 0` ⟹ `h ∈ {a,b}` (**degenerate extra, R_c undefined**).

Indeed `y=0` gives `F_in=F_out` (this half of the identity is valid at `y=0`), and then, since the
mechanism region is under discussion (`F_in ≤ 0`) **and** the closed-domain estimate `F_out ≥ 0` holds,
one gets `0 ≤ F_out = F_in ≤ 0`, i.e. `F_in=F_out=0`. (Do **not** invoke the full product identity at
`y=0`: it contains `R_c`, which is undefined there. The correct chain is
`F_out ≥ 0`, `F_in ≤ 0`, `F_in = F_out` ⟹ all zero.) Hence `h` is at distance exactly `r` from both
`p_in` and `p_out`, and the only such points are the two ring centres `a,b`. At `h=a` the triangle
`(a,b,a)` is degenerate: `R_c` has **no value**, only directional limits. Approaching `h=a+εu`
(`u=(cosθ,sinθ)`) gives
`R_c → d/(2|sinθ|) ∈ [d/2, +∞)` (`d/2<r` since `d<2r` by C879's Lemma 1, but the supremum is `+∞`),
so the face predicate is direction-dependent there — the point is neither "legitimate" nor "missed",
it is a boundary stratum that an `iff` reading must name explicitly.

Two consequences, both consistent with everything already registered:
* `|a|,|b| ≥ |p_out| − r ≥ 1 − r = ρ` (because `|a−p_out| = r`). Consequently a ring centre `a` (or
  `b`) belongs to the closed hub disk `|h| ≤ ρ` **only if** `|a| = ρ` exactly; in general the
  degenerate points lie *outside* the closed hub disk, and the part of the degenerate stratum that is
  inside it is exactly `{a,b} ∩ ∂B(0,ρ)`. In particular the stratum never meets the **strict** domain
  `|h| < ρ`, so **C879's strict statement needs no change** (as the lead noted); only the
  closed-relaxation wording needed repair.
* Corrected closed-domain patch: the mechanism region equals the face region on the closed domain
  **minus the (at most two) degenerate points** `{a,b}∩∂B(0,ρ)`, plus the at most one *missed*
  point `h★` when `y_{h★}>0` (A5, unchanged). Nothing is deleted; the wording "no extras at all" is
  replaced by "no extras with a well-defined face predicate". `AUDIT-CLOSED-H-AND-STRICT-HUB.md` §2
  and `AUDIT-FAN-DISK-MECHANISM.md` §3.3 carry the corrected text.

## 1. Setting, level and quantifiers

Legality per edge (C879): distinct ring centres in `int D`, equal radius `r∈(0,1)`, common covered
boundary arc with exactly one equidistant point. Then for each edge `e_j` the two radius-`r` circle
intersections are `p_in^j∈int D` and `p_out^j∉int D`, and for a **strict** hub `|h|<ρ=1−r`:
face condition for that edge ⟺ `|h−p_in^j|≤r` (inward side + non-collinearity automatic). Hence

> a chain `C=(e_1,…,e_m)` has a strict hub ⟺ `S ∩ B(0,ρ) ≠ ∅`, `S := ∩_{j≤m} B̄(p_j,r)`,
> `p_j := p_in^j`. (C879, unchanged; §0 shows strictness also kills the degenerate strata.)

**Level of §2–§3.** Both theorems are statements about *arbitrary* finite families of closed disks
of a common radius (`m ≥ 1`, arbitrary centres `p_j∈R²`, `r>0`, `ρ>0`). Therefore they hold
uniformly on the whole legal chain domain — no genericity, no separation, no "general position",
no small-`m` restriction, and no restriction on the ring configuration beyond C879's per-edge
hypothesis. The ring data enter only through the algebraic map
`p_j = p_j(c_{i_j},c_{i_{j+1}},r) = m_j − k_j n_j`, `k_j = √(r²−d_j²/4)`, `d_j<2r` — this is the
sense in which all criteria below are **ring-only**.

## 2. Theorem A (finite min-norm candidates)

`S = ∩_{j=1}^m B̄(p_j,r)` is compact and convex (possibly empty). Let

```
C  :=  {0 : 0∈S}
    ∪  { q_j := p_j (1 − r/|p_j|) : p_j ≠ 0, q_j∈S }                     (≤ m points)
    ∪  { z : z ∈ ∂B(p_j,r) ∩ ∂B(p_k,r) for some j<k, z∈S }               (≤ 2·C(m,2) points).
```
(Carry only one copy of coincident disks; identical constraints are redundant.)

**(i)** If `S≠∅` then `C≠∅` and `min_{h∈S}|h| = min_{h∈C}|h|`; the minimiser `q*` of `|·|` over `S`
is unique and belongs to `C`. **(ii)** If `S=∅` then `C=∅` (and conversely), so

> `∃h: h∈S, |h|<ρ  ⟺  min_{h∈C}|h| < ρ ,  and for `S=∅` the answer is "no".

*Proof.* `h ↦ |h|²` is **strictly** convex (`|·|` itself is only convex), and `t ↦ √t` is strictly
increasing, so `|·|` and `|·|²` have the same minimisers and the minimiser `q*` over the convex
compact `S` is unique. If `q*=0` we are in `C_0`. Else `q*∈∂S` (if `q*` were interior, `(1−ε)q*∈S`
would be closer), so `q*` lies on some circle `∂B(p_j,r)`; let `A={j: |q*−p_j|=r}≠∅`. If two
*distinct* disks are active, `q*` is a circle–circle intersection, i.e. in `C_2`. If exactly one disk
`j` is active (after deduplication), then `S` coincides with `B̄(p_j,r)` in a neighbourhood of `q*`
(all other disks are slack), so `q*` is a *local* minimiser of the convex function `|·|²` over the
convex set `B̄(p_j,r)`, hence a global one; the global minimiser of `|·|²` over `B̄(p_j,r)` is `0` if
`|p_j|<r` (then the segment `[0,q*]` stays in the disk and gives closer feasible points,
contradiction) and `q_j` if `|p_j|≥r`. Hence `q*=q_j∈C_1`. ∎

**Degeneracies.** `p_j=0` (disk centred at the origin): the constraint is `|h|≤r`; if `0∉S` the
segment argument excludes this disk as the unique active one, and any point of `∂B(0,r)` that is
also active elsewhere lands in `C_2`. Coincident disks (`p_j=p_k`) are deduplicated. Tangencies
(`|p_j−p_k|=2r`) give one point, kept once. `S` a segment/singleton changes nothing: the minimiser
is still in `C`. The criterion itself uses no constraint qualification, no Slater condition and no dual object; this is a statement about the proof route, not a ban on multiplier arguments elsewhere.
Cost: `1+m+2C(m,2)` candidate tests, each a weak inequality; for the two q0(6,7) fans (`m=4,5`):
17 and 26 candidates.

**Deleted (lead's correction): the earlier "equivalent maximin form".** The claim
`∃h∈B(0,ρ): φ(h)≤r ⟺ min_{h∈B̄(0,ρ)}φ(h)≤r ∧ (argmin set meets B(0,ρ))` is **false**, and is
withdrawn. Counterexample (lead): one pin `p=(2,0)`, `ρ=1`, `r=1.5`: the strict problem is feasible
(`h=(0.75,0)`: `|h|<1`, `|h−p|=1.25≤1.5`) while the minimiser of `φ` over the closed ball is uniquely
`h=(1,0)` on the sphere — the strict feasible point is *not* the closed-ball minimiser, so no
argmin-obstruction exists. The only valid implication in this direction is the trivial one
(strict feasible ⟹ `min` over the closed ball `≤ r`); the converse fails at tangency. The min-norm
form of Theorem A is the correct strict criterion (its minimiser is unique because `|·|²` is strictly
convex).

## 3. Theorem B (strict Helly ≤3-witness disjunction)

Fix a chain with pins `p_1,…,p_m`, radius `r`, hub radius `ρ`. Put
`F = {B(0,ρ)} ∪ {B̄(p_j,r)}_{j=1..m}`, a **finite family of convex sets** in `R²`. Then
`B(0,ρ) ∩ S = ∩_{X∈F} X`. Helly's theorem in the plane (finite families, *no* closedness or
boundedness needed; the open ball is convex) gives:

> **No strict hub ⟺ some subfamily of `F` with at most 3 members has empty intersection.**

Enumerating the subfamilies (singletons are nonempty; `ρ>0`, `r>0`) yields the finite disjunction.
Write `L_{jk} := B̄(p_j,r)∩B̄(p_k,r)` (closed, possibly empty) and
`μ_{jk} := min{|h| : h∈L_{jk}} ∈ [0,∞]` (`=+∞` iff `L_{jk}=∅`), and
`ψ_{jkl} := min_{h∈R²} max_{i∈{j,k,l}} |h−p_i|` = the minimum enclosing circle radius of the three
centres.

| # | subfamily | empty ⟺ | exact algebraic form |
|---|---|---|---|
| W1 | `{B(0,ρ), B̄(p_j,r)}` | `|p_j| ≥ ρ+r` | `|p_j|² ≥ (ρ+r)²`  (tangency counts: the touch point lies on `∂B(0,ρ)`) |
| W2 | `{B̄(p_j,r), B̄(p_k,r)}` | `|p_j−p_k| > 2r` | `|p_j−p_k|² > 4r²` (**strict**: tangency is a common point) |
| W3 | `{B(0,ρ), B̄(p_j,r), B̄(p_k,r)}` | `μ_{jk} ≥ ρ` | test `μ_{jk}` by Theorem A on the 2-disk family (≤5 candidates) |
| W4 | `{B̄(p_j,r), B̄(p_k,r), B̄(p_l,r)}` | `ψ_{jkl} > r` | `ψ = max side/2` if the triangle is obtuse/right, else the circumradius (case split decided by the three dot-product signs) |

and the **no-strict-hub predicate** is `W1 ∨ W2 ∨ W3 ∨ W4` over all indices. Minimal-witness form
(the subsumptions `W1_j ⟹ W2_{jk} ∨ W3_{jk}` for any `k≠j`, and `W2_{jk} ⟹ W4_{jkl}` for any third
`l`, are immediate: if `|p_j|≥ρ+r` and the lens `L_{jk}` is nonempty then
`μ_{jk} ≥ |p_j|−r ≥ ρ`):

> for `m ≥ 2`:  no strict hub ⟺ `∃{j,k}: μ_{jk} ≥ ρ`  **or**  `∃{j,k,l}: ψ_{jkl} > r`;
> for `m = 1`:  no strict hub ⟺ `|p_1| ≥ ρ+r`.

In the `m≥2` form the pair-type case splits into `L_{jk}=∅` (2-set witness, W2) and
`L_{jk}≠∅, μ_{jk}≥ρ` (3-set witness, W3).

*Proof.* Necessity/sufficiency are set inclusion (a subfamily is empty ⟹ the full family is empty;
the full family is empty ⟹ Helly produces a ≤3 empty subfamily). Each row is an elementary
disk-intersection computation: row W1 uses `{|h|: h∈B̄(p_j,r)} = [max(0,|p_j|−r), |p_j|+r]`; row W2
is `|p_j−p_k| > 2r`; row W3 is the definition of `μ_{jk}` (with `μ=+∞` when the lens is empty);
row W4 is the defining property of the minimum enclosing circle (`∩_i B̄(p_i,r) ≠ ∅ ⟺ ψ ≤ r`,
and the MEC of three points is a diameter or a circumcircle). ∎

**Equality semantics (why this is the *strict* version).** The open norm ball forces `≥` in W1/W3
and leaves `>` in W2/W4. The three equality classes are *decided*, not left ambiguous:
`|p_j| = ρ+r` and `μ_{jk} = ρ` **do** witness nonexistence (the tangency point lies on the sphere
`|h|=ρ`, outside the open ball), while `|p_j−p_k| = 2r` and `ψ_{jkl} = r` **do not** (the tangency
point `∈S` is a legitimate strict-hub candidate and is picked up by Theorem A). Using the closed
ball `B̄(0,ρ)` instead would make W1/W3 wrong exactly on these loci.

## 4. CQ failure at singleton/empty closed intersections — what breaks and what does not

Consider the closed relaxation `(P̄)`: `|h| ≤ ρ, |h−p_j| ≤ r` (all `j`), and the strict problem
`(P)`: `|h| < ρ, |h−p_j| ≤ r`. `(P̄)` feasible is **necessary but not sufficient** for `(P)`.

* **Empty closed intersection (`S=∅`).** Then W2/W4 fire (disks alone empty); in multiplier terms the
  norm constraint can take `λ_0 = 0`: a **guaranteed** dual certificate *with* `λ_0>0` is not
  available, and the "≤3 sets counting `B̄(0,ρ)`" pattern must be replaced by a disk-only witness.
  Helly handles this automatically (any empty subfamily counts).
* **Singleton closed intersection on the sphere (`S∩B̄(0,ρ)={q}`, `|q|=ρ`, `S∩B(0,ρ)=∅`).** `(P̄)` is
  feasible, so the closed system has no infeasibility certificate at all, and Slater's condition fails
  by definition (a Slater point would be a strict hub). This is the degenerate case the lead flagged:
  the multiplier/Farkas route gives no *uniform* reading there. The strict version still witnesses the
  answer, and the witness is *robust in form*: `q∈∂B(0,ρ)` and `q` on the active circles forces
  `μ_{jk} ≥ ρ` (or `|p_j| ≥ ρ+r`) for the corresponding subfamily. Example B2/B3 of §6: W1/W3 fire with
  `=0` slack. (Individual multipliers may of course exist at such a point; what is not available is a
  multiplier-based certificate that is uniform over the moving-ring family.)
* **Nonempty closed intersection with no Slater point but a strict hub (`S={q}`, `|q|<ρ`, or more
  generally `int(S)∩B(0,ρ) ≠ ∅` fails).** Then `(P)` is feasible; *no* witness fires (Theorem B is
  exact); but there is no point strictly inside all disks, so a Slater-based dual argument has no
  foothold and LICQ can fail at `q` (tangency of two circles, coincident centres). Theorem A still
  returns the answer and an explicit witness.
* **LICQ-only failure** (`|p_j−p_k| = 2r` at the minimiser): excluded by the same treatment — the
  tangency point is a legitimate candidate of `C_2`.

Summary: the decision procedure of §2/§3 uses **no CQ, no Slater condition and no dual object**
(compactness, strict convexity of `|·|²`, Helly, convexity only). What degenerates at the
singleton/empty loci is the *uniform certificate language* (multipliers, Slater, KKT), not the
criterion. For a moving-ring family this matters: a multiplier-based exclusion is not guaranteed to
cover exactly the boundary strata, while the finitely many algebraic conditions of Theorem B remain
exhaustive.

## 5. Moving rings: the ring-only finite disjunction and its two directions

Fix the chain combinatorics (`m` edges). Since each `p_j` is a (single-square-root) algebraic
function of the two ring centres and `r`, every condition of §2/§3 is a finite Boolean combination
of algebraic conditions in the ring data:

* `Φ(chain) :=` "a strict hub exists for this chain" `= ¬(W1∨W2∨W3∨W4)`, a disjunction of
  `m + C(m,2) + C(m,2) + C(m,3)` algebraic conditions (m=4: 4+6+6+4 = 20; m=5: 5+10+10+10 = 35);
  the reduced minimal form of §3 has `C(m,2)+C(m,3)` conditions (m=4: 10; m=5: 20).
* **Sufficient for exclusion:** proving *one* disjunct on a region of ring data excludes strict hubs
  there (no hub search, no min-norm over a continuum) — each disjunct is local (one pair or one
  triple of pins, i.e. at most 3–4 ring centres).
* **Complete:** if no strict hub exists, one of them holds; hence an *existence* proof must refute
  all of them, and then Theorem A supplies an explicit finite witness. Both directions are finite,
  so the disjunction is necessary **and** sufficient — this is the sense in which the hub continuum
  is eliminated by finitely many ring-only conditions.
* **Equality loci** (where the witness is non-strict, the CQ-failure loci of §4):
  `|p_j|=ρ+r`, `μ_{jk}=ρ`, `|p_j−p_k|=2r`, `ψ_{jkl}=r` (the last two are *not* witnesses). On these
  the verdict is still determined by the `≥`/`>` semantics above; a uniform proof over a closed
  region of ring parameters must treat them explicitly (or perturb off them with the exact
  semantics at the boundary).
* **Interval use:** each disjunct is an inequality between algebraic functions of the centres, so an
  interval/evaluation bound of a disjunct over a box of ring parameters certifies "no strict hub" for
  the whole box; conversely the negation of all disjuncts (a finite conjunction of strict
  inequalities) certifies strict-hub existence with the Theorem-A witness set to be located
  afterwards. Nothing here requires the hub variable to be discretised.
* **Uniformity in `m` and in the ring arrangement.** Theorems A/B do not use the ring origin of the
  pins; the same criterion applies to every legal chain, in particular to the two fans of q0(6,7).

## 6. Instantiation on the certified q0(6,7) object (exact data; no grid)

`n11/upper/certified_object.json` (exact rational centres, `r∈[lo,hi]` with width `4e−60`), 9 ring
sites `{1,3,4,5,6,7,8,9,10}`, hubs `{0,2}` (certified-object labels; lead labels: rings 0..8, hubs
9,10), cyclic order `7,1,8,6,4,9,10,3,5`. The nine pins are recomputed in closed form
(50-digit `mpmath`) and agree with the recorded float64 pins to `≤6e−17`; `|p_out|=1` on all nine
edges. Chain hubs: fan of hub 2 (lead 9) `m=4` with pairs `(5,7),(7,1),(1,8),(8,6)`; fan of hub 0
(lead 10) `m=5` with pairs `(6,4),(4,9),(9,10),(10,3),(3,5)`.

| quantity | fan A: hub 2 (m=4) | fan B: hub 0 (m=5) |
|---|---|---|
| `min_{h∈C}|h|` (Theorem A) | `0.27297746635709771847` (circle–circle) | `0.14942849894640001756` (circle–circle) |
| `ρ − min` (hub margin) | `+0.347039` | `+0.470588` |
| `|hub|` | `0.27297746635709793372` | `0.14942849894640002001` |
| strict hub | **EXISTS** | **EXISTS** |
| W1 slack `(ρ+r) − max_j|p_j|` | `+0.377083` | `+0.470588` |
| pair slack `min(ρ−μ_{jk})` | `+0.347039` | `+0.470588` |
| triple slack `min(r−ψ_{jkl})` | `+0.00144108` (tight triple `(0,1,3)`, ψ branch *diameter*) | `+4.6e−17` (tight triple `(0,2,4)`, ψ branch *circumcircle*, i.e. `ψ=r` at the saturation level) |
| all witnesses fire? | no | no |
| pins active at the hub | 4 of 4 (gaps 49.6°,70.8°,49.6°,190.0°) | 3 of 5 (gaps 95.0°,170.0°,95.0°) |
| closed convexity at the hub | largest gap `>180°` ⟹ escape direction ⟹ `S` not a singleton; **explicit Slater point** `|h|=0.27398<ρ`, strictly inside all four disks (`CQ ok`) | `0∈conv{p_j−hub}` (max gap `≤180°`) ⟹ `S={hub}` at the saturation level ⟹ **no Slater point, CQ unusable**; verdict still by `min|h|=|hub|<ρ` |

So on the certified object the criterion is exercised in **both** regimes: fan A has a Slater point,
fan B is a numerical singleton with no qualifying point at all, and both verdicts come out of the
CQ-free tests with large margins (`0.347`, `0.471`). (Whether the three fan-B saturations
`|hub−p_j|=r` are exact in the certified object is *not* needed for the verdict: the sign of those
`≤1e−17` tails changes neither `min|h|<ρ` nor any witness.)
Cross-check: taking all nine pins in one intersection gives `S=∅` (no single hub serves the nine
edges — consistent with the two-fan structure; not used by the criterion).

Controls (`PART B` of the script, 12 constructed cases, all with the two independent routes —Theorem A
and Theorem B — agreeing; each case is closed-form, no sampling): pair-disjoint (2-set W2);
ball–disk tangency with `|p_1|=ρ+r` exactly (W1 with `=0` slack — the `≥` is load-bearing);
two tangent disks whose lens is the single point `(ρ,0)` (closed singleton, W3 with `=0` slack, CQ
fails); the same lens strictly outside/inside the open ball (witness/no-witness); three disks with
singleton intersection `{q}`, `|q|<ρ` (strict hub exists, no Slater point, `ψ=r` exactly) and
`|q|>ρ` (witness fires); three disks pairwise intersecting with empty triple (only W4 fires);
obtuse MEC branch (projection witness); acute MEC branch (origin witness); collinear triple.

## 7. Scope and non-claims

* Decided here: for **every** legal chain (all `m`, all legal ring data, no genericity), whether a
  strict hub satisfying all its fan face constraints exists, by a finite ring-only disjunction;
  plus the corrected closed-domain classification of §0.
* **Not** decided: the joint problem of the two hubs — the two central triangles
  `R_c(h_A,h_B,c_0)≤r`, `R_c(h_A,h_B,c_4)≤r` (lead labels; `c_0,c_4` = certified-object rings
  `5,6`), hub distinctness `h_A≠h_B`, Delaunay/triangulation validity, and whole-cover sufficiency.
  The two fan criteria yield the two convex feasible sets `S_A∩B(0,ρ)`, `S_B∩B(0,ρ)` (relatively
  open, convex) that the central coupling has to be imposed on; **central coupling remains the
  missing interface**.
* Not claimed: any global radius bound, any statement about covers with fewer/more rings, or that
  the certified object's saturations are exact.
* Theorems A/B are elementary; novelty is not claimed (Helly on disk families and min-norm
  candidates are standard; the content here is the exact `≥`/`>` semantics, the CQ-failure reading,
  and the ring-only packaging).

Repro:
```
py -3 -B -X utf8 research-2026/team-current/r20-geometry/strict_hub_finite_disjunction.py
```
