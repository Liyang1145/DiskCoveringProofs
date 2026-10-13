# Central coupling: retraction of the R⁴ ball/Helly-5 claims; fixed-`a` fiber elimination and the Helly-3 witness enumeration

Author: r20-geometry (sole writer of this directory; no subagents; **no claim registered**).
Status: **correction + replacement** of the earlier version of this file (lead team-message
5a1b74bc). Evidence: `central_active_sets.py/.out.txt/.json`.

## 0. Retractions and corrections (lead-directed; nothing here is registered)

1. **Theorem E (R⁴ balls / convexity / Helly-5 / ≤4-active-ball candidates) is WITHDRAWN.**
   Reason (lead): the central fixed-disk centre `q` depends on the *other* hub `a`; with both `(a,b)`
   moving the constraint is **not** an `R⁴` ball and the feasible set is **not** convex. Even a purely
   `2`-dimensional disk constraint, lifted to `R⁴`, is a **cylinder**, not a ball, so Helly number 5
   and the ≤4-active-ball candidate reduction have no basis. Nothing of that section may be cited.
2. **C894 is retracted and C896 is numeric — neither can serve as a premise.** The registered
   retraction reason of `C894` is a **reversed inclusion** (lead's original reason; no further cause is
   asserted here). The identity used below is the classical one (product identity / extended sine law,
   `lead/R20-CHAIN-HUB-CONVEXIFICATION.md` Lemma 2), stated with its own domain conditions.
3. **Theorem D is corrected.** What survives is only the generic fact: *if* the relevant feasible set
   is compact **and closed**, then a maximiser of a nonzero linear functional has at least one active
   constraint. It is **not** a finite point normal form, and closedness is not automatic here: the
   circumradius is **undefined on the degenerate locus** (`a,b,c` collinear, `a=b`, or `c ∈ {a,b}`),
   so the constrained set need not be closed (a sequence with `R_c ≤ r` can approach a degenerate
   point, e.g. `c → a`). The stratum list D1–D6 is retained only as a **bookkeeping list of candidate
   level sets**, not as a theorem about attainable active sets.

## 1. Fixed-`a` fiber setting (the valid reduction)

Fix `a = h_A ∈ K_A` with both central sites in chord range: `|a − c_a| ≤ 2r`, `|a − c_b| ≤ 2r`
(otherwise the fiber is empty — a finite condition on `a`). For a site `c ∈ {c_a,c_b}` let
`m_c = (a+c)/2`, `d_c = |a−c|`, `k_c = √(r² − d_c²/4)`, `n_c ⊥ (c−a)`, and
`p_±(a,c) = m_c ± k_c n_c` — the two radius-`r` circle centres through `a` and `c` (both exist iff
`d_c ≤ 2r`; at `d_c = 2r` they coincide — the Thales stratum).

**Fiber identity (classical; `lead` Lemma 2 / product identity).** For `b` off the line `ac`, with `y`
its signed height over that line,
`4y²(R_c(a,b,c)² − r²) = (|b−p_+|² − r²)(|b−p_−|² − r²)`, hence

> `R_c(a,b,c) ≤ r  ⟺  b ∈ (B̄(p_+,r) \ int B̄(p_−,r)) ∪ (B̄(p_−,r) \ int B̄(p_+,r))`
> (the closed crescent of the chord `ac`), **and** `b ∉ line(a,c)`.

Equivalently (extended sine law) `R_c = |ab| / (2 sin∠acb)` for non-degenerate triples.

For fixed `a` the fiber constraint set in `b` is a **finite Boolean combination of disks in `R²`**:
`Fib(a) = { b ∈ S_B : |b| < ρ, b satisfies the two crescent conditions }`,
`S_B = ∩_k B̄(q_k,r)` the fan-B pin disks (fixed). The two sites give four branch combinations
`(σ_a,σ_b) ∈ {±}²`; in branch `σ` the constraint is
`b ∈ S_B ∩ B̄(p_{σ_a},r) ∩ B̄(p_{σ_b},r)`, `|b| < ρ`, **and**
`b ∉ int B̄(p_{−σ_a},r) ∪ int B̄(p_{−σ_b},r)`.

## 2. Helly-3 witness enumeration (this directory's new part)

Drop the two "outside" conditions first: the **relaxed fiber** is the disk-intersection family
`F_σ(a) = { B(0,ρ) } ∪ { B̄(q_k,r) }_{fan-B pins} ∪ { B̄(p_{σ_a},r), B̄(p_{σ_b},r) }` in `R²`. It is
convex, so **Helly-3** applies: the relaxed fiber is empty iff a subfamily of at most three of its
members is empty. Enumerating it exactly as in `STRICT-HUB-FINITE-DISJUNCTION.md` §3 (open norm ball;
every condition below is a condition **on `a`**, since `p_σ = p_σ(a,c)` moves with `a`):

| # | witness (relaxed-fiber emptiness) | algebraic form in `a` | semantics |
|---|---|---|---|
| H1 | two fixed pins disjoint | `\|q_k − q_l\| > 2r` | strict |
| H2 | fixed pin vs moving disk disjoint | `\|q_k − p_σ(a,c)\| > 2r` | strict |
| H3 | the two moving disks disjoint | `\|p_{σ_a}(a,c_a) − p_{σ_b}(a,c_b)\| > 2r` | strict |
| H4 | disk vs open norm ball | `\|u\| ≥ ρ + r` for `u ∈ {q_k, p_σ(a,c)}` | weak (`≥`) |
| H5 | open ball + two disks | `μ_{ij}(a) ≥ ρ`, `μ` = min-norm over the two-disk lens by the finite candidate set of Theorem A (origin / projections / circle–circle) | weak (`≥`) |
| H6 | three disks (no ball) empty | `ψ_{ijk}(a) > r`, `ψ` = MEC radius of the three centres (longest side/2 if obtuse/right, else circumradius) | strict (`>`) |

Completeness is Helly-3 plus the elementary disk computations; the `≥`/`>` split is the open-ball
semantics of `STRICT-HUB-FINITE-DISJUNCTION.md` §3. Each witness is an explicit algebraic condition on
the single 2-D variable `a`; hence relaxed-fiber emptiness is a finite disjunction of such conditions.

**Two load-bearing caveats.**

* **Relaxation direction.** The relaxed fiber is a *superset* of the exact branch fiber, so a relaxed
  witness is a valid *exclusion* of that branch (the pruning direction). Conversely, relaxed
  feasibility does not give exact feasibility: the exact branch still needs
  `b ∉ int B̄(p_{−σ_a},r) ∪ int B̄(p_{−σ_b},r)`, i.e. the convex set
  `C_σ(a) = S_B ∩ B̄(p_{σ_a},r) ∩ B̄(p_{σ_b},r) ∩ B(0,ρ)` must not be **covered** by the two forbidden
  open disks. That covering case is a *third* kind of witness (not a Helly-3 disk witness) and must be
  checked separately: `C_σ(a) ⊆ int B̄(p_{−σ_a},r) ∪ int B̄(p_{−σ_b},r)`.
* **Degeneracy/openness.** `R_c` is undefined for `a=b`, `c ∈ {a,b}` and `b ∈ line(a,c)`; the relevant
  sets are therefore **not closed** on this stratum, so no compactness/closedness argument may be used
  without handling it explicitly (this is the corrected content of the old Theorem D).

### 2.1 Sharpened formulas for the two moving central disks (lead-directed; symbolic controls: `central_witness_controls.py/.out.txt`)

Let `p_σ = p_σ(a,c) = m + σ k n` with `m=(a+c)/2`, `d=|a−c|`, `k=√(r²−d²/4)`, `n ⊥ (c−a)` unit
(`σ = ±`), and let `q` be a fan-B pin; all disks have radius `r`. The witnesses involving the moving
disks are then explicit functions of `a`:

* **H2 (pin vs moving disk disjoint)**: `|q − p_σ(a,c)|² > 4r²`. Control C1 verifies symbolically that
  `p_σ` satisfies `|p_σ−a| = |p_σ−c| = r` (the centre genuinely moves with `a`).
* **H3 (the two moving disks disjoint)**: `|p_{σ_a}(a,c_a) − p_{σ_b}(a,c_b)|² > 4r²`.
* **H4 (disk vs the open hub ball)**: `|u|² ≥ (ρ+r)²` for `u ∈ {q, p_σ(a,c)}` (weak: tangency counts).
* **H5 (open hub ball + the two moving disks)**: explicit candidate set
  `C = {0 (if in both disks)} ∪ {p_j(1 − r/|p_j|) : j ∈ {σ_a,σ_b}, if in both} ∪ {∂B(p_{σ_a},r) ∩ ∂B(p_{σ_b},r) (≤2 points, tangency counted once), if in both}`,
  witness `μ := min_{h∈C}|h| ≥ ρ` (weak), where **the minimum is taken over the candidates that lie in
  the lens** `L = B̄(p_{σ_a},r) ∩ B̄(p_{σ_b},r)` (each candidate is filtered by both disk inequalities;
  unfiltered minima are not used), with the convention `μ = +∞` if `C ∩ L = ∅`. *Control C4*: the tangency configuration (`ρ = 1/2`, two
  radius-`1/2` disks tangent at `(ρ,0)`) gives `μ = ρ` exactly, so the `≥` semantics is load-bearing; a
  strict configuration fires with margin.
* **H6 (three disks empty: 2 moving + 1 pin), orientation-free polynomial form.** With centres
  `P_1 = p_{σ_a}`, `P_2 = p_{σ_b}`, `P_3 = q`, put `a₂ = |P_2−P_3|²`, `b₂ = |P_3−P_1|²`,
  `c₂ = |P_1−P_2|²`, `X = cross(P_2−P_1, P_3−P_1)` (only `X²` appears):
  > `MEC > r  ⟺  [max(a₂,b₂,c₂) > 4r²]  ∨  [a₂ < b₂+c₂ ∧ b₂ < c₂+a₂ ∧ c₂ < a₂+b₂ ∧ a₂b₂c₂ > 4r²X²]`.
  **Correction of the first bracket's scope (lead):** `max edge > 2r` is a **sufficient** condition for
  `MEC > r` for *every* triangle (the MEC contains the longest pair, so its diameter is at least the
  longest side), and it is *equivalent* to it in the obtuse/right/collinear case (there the MEC radius
  equals longest/2). It is therefore **not** restricted to obtuse triangles; the second bracket only
  supplies the residual acute case (`longest ≤ 2r` while `R > r`), testing acuteness by the three
  orientation-free inequalities and the circumradius via `R² = a₂b₂c₂/(4X²)`; `X = 0` leaves only the
  first bracket. *Control C2*: the equivalence
  matches on all exact-rational instances, and the **obtuse control** `(0,0),(2,0),(1,1/20)` has
  `R² = 160801/1600 > r² = 1` while `MEC² = 1 ≤ 1` — testing `R > r` alone would be **wrong**; the
  acuteness clause is load-bearing. *Control C3*: `a₂,b₂,c₂,X²` are invariant under an exact rational
  rotation and a reflection (and under permutations). H1/H2/H3 are the pair cases of the first bracket;
  H6's second bracket is the only genuinely 3-point clause.

### 2.2 Interface with the distal-exclusion test (`alternative`) — **conditional only, no δ cited**

`alternative` (`r20-alternative/CENTRAL-HELLY-SCREEN.md`) states a conditional equality: the
single-disk excess over the exact crescent is a half-lens contained in the far disk `B(q'_i(a),r)`, so
**if** `K_B ∩ B(b_B,ε_B) ∩ B(q'_i(a),r) = ∅` **then**
`{b : ρ(a,b,c_i) ≤ r} = R ∩ B(q_i(a),r)` on `R = K_B ∩ B(b_B,ε_B)` — an equality, not a relaxation.
In boxes where this conditional hypothesis is verified, my caveat (i) (the third, "covering-type"
witness) disappears.

**δ retraction (lead, c498de5a).** The previously quoted numeric box radii (`δ ≤ 1.872·10⁻³` etc.) are
**withdrawn and must not be cited**: the lead found float weights, a bbox-endpoint error and a `sqrt`
domain error in `alternative`'s code; the old δ is **not certified** and the code is being repaired.
Only the **conditional** statement above may be cited (and only as a hypothesis, box-level, at the time
its re-certified version appears).

**v2 numbers (reported by `alternative`, 6485df2f — recorded, NOT cited).** Their repaired v2 gives
`ε_A = 5.905046376·10⁻⁹`, `ε_B = 0.033062070669`, and box-level (H2) ranges
`δ ≤ 1.8720480434·10⁻³` (fixed `r`) / `δ ≤ 1.8200529466·10⁻³` (`r` window `±10⁻⁴`); `δ = 1.9·10⁻³`
fails at face 4 (`G₄` lower bound `6.58·10⁻¹³`), `δ ≥ 0.05` is explicitly UNDECIDED (pin-root
choice). Their stated domain is *C879-legal tuples only* (a tuple with both roots inside the unit disk
is not legal and is outside their claim). **Per the lead's c498de5a instruction, these values are
recorded but remain uncited** until an independent audit of the v2 code (signed output, per-`sqrt`
contracts, outer scalar bbox, `r₀ = UB*`) confirms them; only the **conditional** (H2) statement of
§2.2 may be used, and only as a hypothesis.

### 2.3 Algebraic sign-case representation of H5/H6 (denominator-ised) — for fiber exclusion, **not** a CAD sweep

Purpose (lead): supply an algebraic sign-case representation usable for **actual fiber exclusion** on
a region of `a`; it is *not* an invitation to assert global CAD conclusions.

**H6.** `MEC > r` is written as the disjunction of two sets of **polynomial** conditions in the centres:
`max(a₂,b₂,c₂) > 4r²` and `[acuteness: three linear-in-a₂b₂c₂ inequalities] ∧ a₂b₂c₂ > 4r²X²`. With
`P_1 = p_{σ_a}(a,c_a) = m_a + σ_a k_a n_a`, `k_a² = r² − d_a²/4`, `d_a = |a−c_a|`, and likewise for
`P_2`, each squared side and `X²` is a polynomial in `a` and the radicals `k_a, k_b` of **degree ≤ 2 in
each radical** (control C5), and after reducing by `k_c² = r² − d_c²/4` the monomial support is
contained in `{1, k_a, k_b, k_ak_b}` — i.e. the reduced clause is **linear in `(k_a, k_b, k_ak_b)`**
(C5 verifies this, including the raw terms `k_ak_b², k_a²k_b, k_a²k_b²` of `X²` that reduce only via
the squared-radical substitution). Isolating one radical and squaring
therefore adds at most **two sign cases** per clause (the sign of the coefficient of the remaining
radical), giving a finite list of polynomial conditions in `a` with explicit sign cases and no CAD.
The pin centres `q` contribute no radicals. (Earlier draft wording "affine in each radical before the
substitution" was wrong and is corrected: the quadratic-in-radical terms are exactly what the
substitution eliminates.)

**H5.** `μ(a) ≥ ρ` is written without minimisation as the finite **conjunction over the five candidate
slots** `h ∈ {0, π_1, π_2, z_1, z_2}` of
`¬( |h−p_{σ_a}|² ≤ r² ∧ |h−p_{σ_b}|² ≤ r² )  ∨  |h|² ≥ ρ²`
(“candidate outside the lens, or at distance ≥ ρ from the origin”), with `π_j = p_j(1 − r/|p_j|)`
carrying the radical `|p_j|` and `z_{1,2}` the circle–circle radical `hh = √(r² − (|p_1−p_2|/2)²)`
(tangency `hh = 0` gives one slot, counted once). Clearing each clause gives polynomial conditions in
`a` plus the finitely many sign cases for the radicals `|p_j|, hh` (all ≥ 0 by construction), with the
lens-membership filters of §2.1 kept in the clause (`unfiltered` minima are **not** used).

Every clause is thus an algebraic condition on `a` with a finite case list, ready to be combined with
the witness loci for fiber exclusion; no claim is made here about the global `a`-plane.

## 3. What remains, and who owns it

Eliminating `b` fiber-by-fiber leaves a **2-D problem in `a`**: find `a ∈ K_A` for which `Fib(a) ≠ ∅`,
i.e. avoid the finite union of the witness conditions H1–H6 (plus the covering witness).

* The `a`-plane is cut by the finitely many witness loci (algebraic curves/points) into finitely many
  cells on which the relaxed-fiber verdict is constant: the remaining task is a finite cell
  enumeration (this is the finite structure that survives; the `a`-side reduction is owned by
  lead/`alternative`).
* Any convex relaxation of the `a`-side must be assembled from disk constraints **in the `a`-plane**,
  not from `R⁴` balls/cylinders (retraction §0.1).

Instantiation on the certified object (bookkeeping only, **no normal-form claim**):
`d = |h_A−h_B| = 0.422405965303498`, `α_d = arcsin(d/2r) = 0.589350176369399 rad = 33.7673°`, and both
central angles equal `α_d` exactly (both central constraints tight, `R_{c_a} = R_{c_b} = r`),
`c_a`/`c_b` on opposite crescent sides, fan A has an active pin disk (`−2.34·10⁻¹⁶`), fan B is slack
(`−2.84·10⁻³`), both hubs strict.

## 4. Scope / non-claims

* **Withdrawn:** Theorem E (R⁴ balls, convexity, Helly-5, ≤4-active-ball candidates) — no basis.
* **Corrected:** Theorem D — only the generic compact-boundary fact, with explicit closedness
  hypotheses; the degenerate stratum (undefined circumradius) breaks closedness and needs separate
  treatment.
* **Provided:** the fixed-`a` fiber reduction with the Helly-3 witness enumeration H1–H6 and its two
  caveats; the remaining 2-D `a`-problem with owner boundary.
* Not claimed: any global exclusion, any certificate, any use of C894/C896 as premises; nothing
  registered.

Repro:
```
py -3 -B -X utf8 research-2026/team-current/r20-geometry/central_active_sets.py
```
