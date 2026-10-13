# Joint reduction (arc ledger + two-hub separating line): the minimal new obligation

Author: flash-structure. Write scope: `research-2026/team-current/flash-structure/`.
Status: **analytic + numeric**; no optimality conclusion; no claim of the main target.
Question answered (lead): is "the nine actual arcs are each essential" enough to give no triple
overlap / only cyclic adjacent overlap; how to parameterise all legal overlaps; what is the minimal
new obligation of the joint reduction — hub-cell adjacency, or non-adjacent ring-ring chord exclusion?

---

## 1 The ring side is closed (no new assumption, no `Σt = π` WLOG)

For `0<r<=19/50` the reduction gives nine boundary disks + two strictly interior disks
(`solo-20260922/N11-LOW-RADIUS-REDUCTION.md`). For the nine **actual** arcs:

* the arc of disk `i` has half-width `t_i = arccos((1+a_i^2-r^2)/(2a_i)) <= asin r`
  (because `(1+a^2-r^2)/(2a) >= sqrt(1-r^2)` by AM–GM), so `2t_i <= 2 asin(0.38)`;
* `16 asin(19/50) < 2π` (equivalently `19/50 < sin(π/8)`, exact by squaring: `5776 < 5858`),
  so **any eight of the nine arcs have total length `< 2π` and cannot cover ∂D**; as the nine arcs do
  cover ∂D, **every one of them is essential**. This premise is therefore automatic, not assumed
  (`team-max-20260922/n11-structure/ARC-Q2-CHECK.md` §L3 states it; re-derived here, incl. the AM–GM
  step that fails for centres inside D if one forgets it).
* With essentiality, the lift argument gives: no containment, strictly increasing left/right
  endpoints on the double lift, adjacent arcs meet, non-adjacent arcs are disjoint, multiplicity ≤ 2
  (**no triple overlap on ∂D**), and the staircase order
  `L_1 ≤ R_9 < L_2 ≤ R_1 < … < L_1+2π ≤ R_9`. Two independent audits exist
  (`n11-hole/AUDIT-ARC-COORD-P2P1.md`, `c450-review/9plus2-next/ARC-LEMMA-AUDIT.md`); I re-derived
  all of it and found no gap (the only repairs needed were textual and are recorded there).
* **All legal overlaps** are therefore exactly the ledger domain
  `L_r = {0<t_i<=asin r, o_i>=0, Σo = 2Σt-2π, ℓ_i = 2t_i-o_{i-1}-o_i > 0}` with
  `o_i = t_i+t_{i+1}-γ_i` the actual arc overlap, `γ_i` the centre angle gap; the map
  `(t,o) ↔` (arc family mod rotation) is a bijection (17 parameters mod rotation).
  **No genuine WLOG `o_i = 0` / `Σt = π` is available** (the inner-root replacement is an
  *existence* reduction on centres, not an overlap removal); this is the bridge the lead flagged.

## 2 General-ledger geometry (new, replaces the touching-only tip formula)

Inner root `ρ(t) = cos t - sqrt(r²-sin²t)`, `c_i = ρ(t_i)u(φ_i)`, `φ_{i+1} = φ_i + γ_i`.
For two adjacent circles (`d_i = |c_i-c_{i+1}|`):

```
crossings  v_± = M ± h·n⊥,  M = (c_i+c_{i+1})/2,  h = sqrt(r²-d_i²/4),  n⊥ = rot_{-90}(c_{i+1}-c_i)/d_i
|v_±|²      = ρ_iρ_{i+1} cos γ_i + r² ± ρ_iρ_{i+1} sin γ_i · cot β_i ,   sin β_i = d_i/(2r)
```
(**sign convention corrected after lead review, item 2.** Since `n⊥ = rot_{-90}(c_{i+1}-c_i)/d_i` and
`n⊥ ∥ u(mid)` for equal radii, one gets `M·n⊥ = ρ_iρ_{i+1} sin γ_i / d_i > 0`; hence `v_+ = M+h·n⊥`
carries the **plus** term and is the outer (∂D-side / outside D for `o_i>0`) crossing, `v_- = M-h·n⊥`
the inner one. Writing `∓` was wrong.) Both identities verified symbolically and numerically against
direct crossings. Consequences (dense 3-parameter scans, `out/run3_pair_scan.txt`, 5.8e6 samples per
`r`, `r ∈ [0.36,0.38]`):

* `|v_-(inner)| < 1` always (max `0.9118`), `|v_+(outer)| >= 1` always with **equality iff `o_i = 0`**;
  in the touching case `v_+ = u(φ_i+t_i)` and `|v_-|² = 2ρ_iρ_{i+1}cos γ_i + 2r² - 1`, i.e. the
  formula used in the repo (`hole-2center/THEOREM-C.md` C1, `TIPS-DISCIPLINE.md`) is exactly the
  `o=0` specialisation. For `o_i>0` the outer crossing leaves `D`; **the tip formula of the repo does
  not generalise without the `cot β` term.**
* `B(0,a*) ⊆ cl(H)` holds for every ledger: `dist(0,B_i) = ρ_i - r >= a* := min_kρ(t_k) - r`
  (the point of `B(0,a*)` nearest to `c_i` is at distance `>= r`; equalities allowed). This is A1 without
  the touching assumption.
* `V_j ⊆ B(h_j,r)` for the hub cells (lead note §2) and `cl(H) ⊆ V_1 ∪ V_2` (N1, see the review file).
  So the hub bisector `L` is the canonical separating line, and each point of `cl(H)` belongs to a hub
  **cell**, not merely to a hub disk.

## 3 The two-hub criterion: the correct bisection class is the *line-separable* one

Let `v_1..v_9` be the nine inner crossings ("tips") and `S_±` the tips on the two sides of `L`.
Chain: `v_k ∈ cl(H)` (obligation O1 below) and `cl(H) ⊆ V_1∪V_2` (N1) and `V_j ⊆ B(h_j,r)` (note §2) give

```
(O2)  MEC(S_+) <= r  and  MEC(S_-) <= r      [each class is inside one hub disk]
(O3)  α̃(m_+) + α̃(m_-) >= π ,  m_± := max_{v∈S_±}|v| ,
      α̃(m) := π  if m-r <= r-a*  (hub disk contains the whole circle C(a*));
              arccos((a*²+(m-r)²-r²)/(2a*(m-r)))  if |m-r-a*| < r ;   0  if m-r >= r+a*
```
**(branch structure added after lead review, item 3.)** The plain formula
`α(s) = arccos((a*²+s²-r²)/(2a*s))` is undefined at `s = 0` and outside `[r-a*, r+a*]`; the correct
object is the *arc half-width of `C(a*) ∩ B(h,r)`*: full circle (`π`, i.e. the whole circle is
covered) when `s <= r-a*`, the arccos branch when `|s-a*| < r`, and empty (`0`) when `s >= r+a*`. With
`a* < r` (A2) the extension `α̃(0) = π` used in the repo is consistent, `α̃` is continuous and
non-increasing on `s >= 0`, and `s_j >= m_j - r` (from `|v| <= |v-h_j|+|h_j| <= r+s_j`) gives
`α(s_j) = α̃(m_j-r)` in the sense `<=`, so O3 with the tilde is the valid necessary form.

**The C618 shortcut does NOT transfer to general `o` (lead review item 3).** The touching-family
estimate `|v_k| <= 1-2r²` (from `|v_k|² = 2ρ_kρ_{k+1}cos γ_k + 2r² - 1 <= (1-2r²)²`) rests on the
touching formula; for `o_k > 0` the `cot β` term changes the bound and the estimate no longer follows.
Scope of the failure: on **local pair data** `(t_k, t_{k+1}, γ_k)` the estimate is violated —
`out/run3_pair_scan.txt` reaches `|v_in| = 0.9155` at `r = 0.3601` versus `1-2r² = 0.7407`, and
`0.9118` at `r = 0.38` versus `0.7112`; in the **sampled full legal ledgers** the maximum stayed at
`0.7089` (r=0.38) / `0.739987` (r=0.3601) — i.e. close to `1-2r²` — so the bound may still hold on the
ledger domain, but it would need its own proof and must not be inherited.
So in the general ledger the side condition `(m_j-r)² < a²+r²` needed to replace `a*` by a uniform
`a_lo` must either (i) be avoided by stating O3 with the **actual** `a*` (recommended: the criterion is
then still a valid necessary condition and no side condition appears), or (ii) be re-established by a
new proof. Likewise the crude bound `m_j < 1` only gives `(1-r)² < a_lo²+r²`, i.e. `a_lo² > 1-2r`,
which fails at `r = 0.38` (`a_lo = 0.2404 < sqrt(0.24) = 0.4899`).

**De-parameterisation (corrected after lead review, item 4).** `S_±` are cut by a *line*, so the
correct quantifier is over **line-separable subsets** of the nine tips (at most `O(n²)` of them, here
≤ 81) rather than over all `2^9 = 512` bisections. What may and may not be claimed:

* *validity*: the hub classes are Voronoi classes (N1) and are separated by `L`, hence line-separable. ✔
* *the pure MEC part (O2) is EQUIVALENT for the two families*, not stronger: if two equal disks cover
  a finite point set, each side of their perpendicular bisector is contained in the corresponding disk
  (the C539 bisector argument), so any bisection with both MECs `<= r` yields a line-separable
  bisection with the same property. Therefore C619/C622's "must use all subsets" verdict stands for
  the MEC-only statement, and `Λ_j^{all}` is the right object there.
* *what the linear form does give*: (i) an **enumeration reduction** (≤ `O(n²)` classes instead of
  `2^n`) — the criterion becomes a 1-parameter family of cuts per pair, no longer a `2^9` scan; and
  (ii) the capacity condition (O3) is **class-specific** (`m_±` depends on the class), so restricting
  the classes cannot weaken the conjunction; the *size* of that gain is NOT quantified here and the
  earlier phrase "strictly stronger" is **withdrawn**.
* *contiguity (corrected)*: line-separable = contiguous only if the nine tips are in convex position,
  which is **false in general**: in 10,500 sampled legal ledgers, 1,959 have non-convex tips (usually
  8 hull vertices, typically when one overlap of `o ≈ 17–20°` concentrates the angular budget). So for
  those ledgers the linear family strictly contains the contiguous family, i.e. a criterion restricted
  to contiguous classes is **not equivalent** to the linear one. Whether an actual feasible
  configuration (hubs included) can exhibit a *non-contiguous* hub class is **open**; the earlier
  phrasing that "consec can be unsound" is **withdrawn** — it would need a legal counterexample with
  hubs, which is not claimed. The record configuration *is* convex (9 hull vertices) and its
  line-separable split is contiguous (5+4).

## 4 Minimal new obligation

**(O1) Tips lemma (general ledger).** For every legal ledger and every adjacent pair, the crossing
inside `D` satisfies `v_k ∉ int B(c_j)` for all `j ∉ {k,k+1}`; equivalently (with the wedge remark
below) `v_k ∈ cl(H)`.

**⚠ Scope correction after C789 (flash-compute).** The *unrestricted* tips lemma is **false
numerically**: a strictly legal ledger exists (their `o1_counterexample_strict-legal.json`, `r = 0.38`)
in which the pair-0 tip falls inside a third ring disk with margin `-7.5666e-2`. Their failing index is
`k+2`, i.e. **inside** the proved candidate set, and the ledger is **not cover-extendable** (best
residual two-hub MEC `0.6116 > r`, O2 fails). Therefore the statement actually needed by the chain is
the **cover-extendable** version: *if the ring can be completed to a covering by two radius-`r` disks,
then `v_k ∈ cl(H)` for all `k`* — and the two-neighbour **reduction is unconditional** (it is ring-only,
§LOCALITY-LEMMA-RING.md), so C789 corroborates it.

Evidence (own instruments):
* 42,000 random legal ledgers, `r ∈ {0.3601, 0.36603, 0.3700, 0.3750, 0.3775, 0.37998385, 0.38}`:
  margin `min_{j∉{k,k+1}} |v_k-c_j| - r` is positive in **every** case; worst `+2.62e-3` at `r=0.38`
  (a ledger with 20° excess concentrated in one overlap), `+1.30e-2` over the uniform sampler
  (`out/run2b_ledger_stress.txt`, `out/run4_structure_stats.txt`).
* record configuration: worst margin `+0.2443`, and all nine tips admit an explicit radial-ray
  witness inside `H`.
* the *radial* ray is not always a witness (2/42,000 ledgers have it marginally covered,
  `-1.2e-6`), so a proof must use the local wedge at `v_k` (the sector
  `{w : w·(v_k-c_k) > 0 and w·(v_k-c_{k+1}) > 0}`), not the radial direction.
* Status: **numeric only**. This is the load-bearing premise of O2/O3 — nothing else in the chain is
  conditional.

### 4b O1: only `j = k-1, k+2` are possible (proved reduction), plus two usable inequalities

**Step 1 — the candidate set is proved to be `{k-1, k+2}` (locality lemma, `LOCALITY-LEMMA-RING.md`).**
`v_k ∈ B_k ∩ B_{k+1}`. If `v_k ∈ B_j` for some `j`, then:
* `g(k,j) >= 3` (cyclic index distance) is impossible, because two ring disks at index distance `>= 3`
  are **disjoint** (L1: their two arcs would sit in `J = ∂D ∩ B(p,2r)`, the staircase would push
  `g-1 >= 2` further arcs into `J`, so `|T| >= g+1 >= 4` arcs in `J`, contradicting
  `π <= asin(2r) + 5 asin(r) < π`);
* `j = k-2` is impossible, because then the three disks `k-2, k, k+1` would share `v_k`, and three
  ring disks with a common point must have consecutive indices (L2); but `g(k+1,k-2) = 3`.

Hence `v_k ∈ B_j` only for `j ∈ {k-1, k+2}` (mod 9): **O1 ⟺ `|v_k - c_{k-1}| >= r` and
`|v_k - c_{k+2}| >= r`.** This is a *proved reduction* (capacity counting), not the withdrawn
scalar-ordering argument; the retracted C784 and its `ρ_j sin δ_j` ordering play no role.

**Step 2 — how to certify the two remaining inequalities.** For `v = v_k` and `δ_j` the **cyclic**
angular distance between `arg v` and `φ_j` (`c_j = ρ_j u(φ_j)`), `δ_j ∈ [0,π]`, exactly:

```
|v - c_j|²  = |v|² + ρ_j² - 2|v|ρ_j cos δ_j ,   ρ_j >= 1-r  (inner root, t_j > 0),  r <= 1/2
     δ_j >= π/2   =>  cos δ_j <= 0  =>  |v - c_j|² >= ρ_j² >= (1-r)² >= r²       =>  FREE
     δ_j <  π/2   =>  |v - c_j| >= ρ_j sin δ_j   (min over |v| of the quadratic at |v| = ρ_j cos δ_j)
```

so each of the two inequalities is implied by `ρ_j sin δ_j >= r`, and by the coarser sound forms
`(Coarse A) ρ_j sin δ_min >= r` (common angle `δ_min := min_j δ_j`) and
`(Coarse B) [δ_min >= π/2] or [(1-r) sin δ_min >= r]` (universal `ρ_j > 1-r`).

**Withdrawn (C784, lead review) — kept for traceability.** The former claim that monotone growth of
`δ_j` forces monotone growth of `ρ_j sin δ_j`, hence that only `j = k-1, k+2` can bind, was **false as
argued** (`ρ_j` may shrink faster than `sin δ_j` grows), and the companion assumption
`arg v ∈ (φ_k, φ_{k+1})` is false in general (`σ := arg v - φ_k = 36.6° > γ_k = 23.7°` for a tiny-arc
ledger at `r = 0.36`), so `δ_{k-1} = σ + γ_{k-1}`, `δ_{k+2} = γ_k + γ_{k+1} - σ` hold only inside the
local window and the cyclic form must be used. The *conclusion* "only `k-1, k+2`" is nevertheless true
— but through Step 1's capacity count, not through scalar ordering. Consequence: the all-j condition
one of the coarse substitutes is what remains; **no two-neighbour criterion is claimed**.

* the certified part is component-wise: each inequality `|v-c_j| ≥ ρ_j sin δ_j` is a two-line
  calculation, so the sufficient conditions above are analytic, not numerical;
* if the margin is strictly positive then the whole open wedge
  `{w : w·(v-c_k) > 0, w·(v-c_{k+1}) > 0}` at `v` is outside every other ring disk, and
  `v ∈ int D`, so `v_k ∈ cl(H)` follows (wedge — not radial direction — as witness).

**Domain of the local-parameter reduction (explicit, per lead).** With Step 1 the conditions are the
*two* inequalities `|v_k - c_{k-1}| >= r`, `|v_k - c_{k+2}| >= r`.
* *Touching family only* (`o ≡ 0`, hence `Σt = π`, `γ_i = t_i + t_{i+1}`): each inequality depends on
  the **three** local parameters `(t_{k-1}, t_k, t_{k+1})` (resp. `(t_k, t_{k+1}, t_{k+2})`); this is
  where a `Σt = π` argument is legitimate.
* *General ledger* (`o >= 0`, **no `Σt = π`**): they depend on the **five-plus** local quantities
  `(t_{k-1}, t_k, t_{k+1}, t_{k+2}, γ_{k-1}, γ_k, γ_{k+1})`, tied by the global constraints
  `Σγ = 2π`, `Σo = 2Σt - 2π`, `o_i >= 0`, `ℓ_i > 0`; a proof for the general ledger must use these
  constraints, not the touching ones.

Uniform bounds available for the case analysis: `ρ_j > r`, `ρ_j <= sqrt(1-r²)`, `γ_i > |t_i-t_{i+1}|`,
`γ_i <= t_i + t_{i+1}`, plus the global constraints above.
Sanity check only — **not certification** (own instruments; float64; record configuration + 600
structured legal ledgers): EXACT all-j margin `+0.2295` (record) and `+0.14496` (grid worst);
COARSE-A `+0.16505` / `+0.12517`; COARSE-B `+0.10217` / `+0.03106`; direct margins `+0.2443` /
`+0.15441`. Note that the *sound two-number* criterion COARSE-B is strictly weaker but still positive
on this set, which makes it a plausible single-inequality target for the analytic O1 proof;
`out/run7_o1_reduction.txt`, `tools/run7_o1_reduction.py`.

**Verdict on the two candidates the lead asked about.**

* *Hub cells adjacent?* Not the minimal obligation, and not independent: `cl(H) ⊆ V_1 ∪ V_2` (N1),
  both `V_j` closed convex, `H ∩ V_j ≠ ∅` (each hub is non-deletable, and a point covered only by hub
  `j` is in `H`), so **hub adjacency follows from connectedness of `cl(H)`**. It is not automatic:
  non-adjacent ring disks do overlap inside `D` (e.g. `r=0.38`, `t≈20°`: `|c_i-c_{i+2}| ≈ 0.53 < 2r`)
  so "pockets" are conceivable. Numerically the record configuration has `H` connected (1 component,
  `1400²` grid) and the hubs Delaunay-adjacent; no payoff of hub adjacency for the criterion has been
  identified, so it should not be promoted to the next obligation.
* *Non-adjacent ring-ring chord exclusion?* Also not needed: the Euler count `v<=11`, `e<=21` uses only
  degree `>= 3`, and the two-hub criterion never uses ring-ring Voronoi adjacency. It holds in the
  record configuration (0 non-consecutive ring-ring Delaunay chords among 21), and the four-ring lemma
  already forbids its degenerate form (no 4 ring cells at an interior vertex). Its only role would be
  to pin the Delaunay wheel structure.

## 5 Exact shape of the resulting unconditional chain (what remains)

```
9+2 structure (C450/C451, conditional reference)
 -> ledger (t,o) in L_r                        [PROVED, no o=0 assumption]
 -> explicit crossings v_k(t,o), a*            [PROVED, §2 here]
 -> B(0,a*) ⊆ cl(H)                            [PROVED, §2 here]
 -> cl(H) ⊆ V_1 ∪ V_2, separating line = L     [PROVED, N1 + note §2]
 -> v_k ∈ cl(H)                                [OPEN: O1; reduced to two scalar inequalities per pair, \
                                                 numeric margin >= 2.6e-3 over 52,500 ledgers; §4b]
 -> O2 (line-separable classes, MEC <= r) + O3 (branch-aware α̃ capacity with the actual a*)  [derived]
 => exclusion criterion: for all ledgers and all lines, O2 or O3 fails
```
Reproduction: `py -3 -B -X utf8 tools/run1_fammin_structure.py` (record config),
`tools/run2b_ledger_stress.py` (42,000 ledgers), `tools/run3_pair_scan.py` (pair geometry),
`tools/run4_structure_stats.py` (convex position / line-separability), `tools/run5_analytic_checks.py`
(four-ring lemma + degree-3 repair), `tools/run7_o1_reduction.py` (O1 reduction consistency).
