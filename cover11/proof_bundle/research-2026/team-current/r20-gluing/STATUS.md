# r20-gluing — STATUS (round 20, cline2 / DS v4.1f, single member)

> **2026-09-24 successor note (cline2 DS v4.1f, cline2-r20-gluing inherited).** See
> `REPORT-R20-FINAL.md`. Instrument rebuilt from the authoritative producer
> `lead/q0_lower375_dual.py`: 78 independent parameters (11×(a,b,y) + 9×(b,y) + 9×(α,u,v)),
> affine stationarity `v' + M'·z` (calibrated to 1.0e-10), ETA identically 0
> (`r20_prod_check.py`: 0 ETA coefficients), cone = `z[eta]=0, z[50:71]≥0, z[71]≥0`, all other
> columns free. Caliber R = r_cand everywhere. Value match at the candidate:
> `const(z_c825) + Σ(v_k + M_k·z_c825) = π` to 3.1e-15.
>
> **Bounded reading (10 competition exchanges, cuts from true factor-wise maximisers,
> 29 independent 1D/2D/3D problems):** LP stays feasible but no witness closes —
> worst factor excess +8.9e-2 (|z|∞≤3), +7.6e-2 (≤1e3), +2.6e-2 (≤1e6). Verdict
> **numerically inconclusive, leaning no-support**; not a disproof, no claim registered.
> Superseded/withdrawn: the predecessor's `V = 1092` family reading, the 78D-BnB next action,
> and the "ETA firing on rings 3–8" structural claim. See DEAD.md §9–12.
> Earlier quarantined versions (wrong caliber R = 19/50, 69 shared parameters, homogeneous
> stationarity, reversed boundary signs, improvised cone) remain in `quarantine/` as
> non-bearing history.


Object: unconditional sharp n11 optimum (proven floor C825 `r_D(11) > 3/8`, ceiling C249
`0.3799838531198386897`). All work here is **diagnostic/calibration**; **no claim registered**,
lead kernel untouched (read-only).

## Established this round (all calibrated numerics, not proofs)

1. **Factor implementation calibrated** on the certified C825 instrument: all 29 pointwise
   maxima at R=3/8 lie inside the certified `[lower, upper]` bands; gaps ≈ the B&B tolerance.
   → `r20_factor_probe.json`.
2. **Residual definitions calibrated** on the saved genuine candidate (`r = 0.3799838531198388`):
   site/hub angle sums, cyclic closure, Σw−2π, both radius-copy families, both side-matching
   families and direct sine-law side gaps all ≤ 1.1e-15; Delaunay slacks ∈ [0.502, 1.963].
   → `r20_candidate_calibration.json`.
3. **Exact gap identity** `V(z) = A(x*) + Σ_c (±)z_c g_c(x*)`, verified ≤ 2.2e-15 at R=3/8 and
   R=19/50.
4. **High-value combination** of the strongest saved pure 29-factor solution
   (`lead/q0_lower375_dual_0_4.json`, certified at R=3/8) at R=19/50: `V = 3.188780840078`,
   `V − π = +0.047188`; argmax is the all-radii-saturated corner (`y_face ≡ y_sw ≡ 1`,
   `u,v ≈ 1`); weighted terms: `A − π = +0.116128`, `m2 = −0.045479`, `closure = −0.044445`,
   `m1 = +0.020165`, copies ≈ ±0.004, angle sums −0.0017.
5. **Two sector-chain couplings are EMPTY at this solution** (falsified as "the missing
   coupling"): radius sharing gain ≤ 1.8e-5 (cycle DP, optimum at `y ≡ 1`); closure-imposed
   switch angle gain ≤ 4.2e-4. → `r20_mechanism.json`, `r20_closure_coupling.json`.
6. **Gap is diffuse**: `V − π = Σ_k δ_k = 0.047188`, faces 0.026285 / rings 0.015803 /
   switches 0.005100, largest single δ = 0.006397 (13.6 %). → `r20_gap_decomposition.json`.
7. **Not gluable at all**: the 21 shared-side equalities are linear in the 20 log-radii with a
   2-dimensional left null space (cycle rank `E−V+1 = 2`); the holonomy defect is 0.0 at the
   genuine candidate and **0.013953** at the high-value combination ⇒ no radii assignment can
   match the shared sides at those angles. → `r20_holonomy.json`.

## Proposal on the table (falsifiable, unproved)

**P-R20-2**: the two holonomy conditions `u_jᵀ rhs(angles) = 0` are a valid, minimal, and not yet
imposed addition (necessary: defect 0.0 at the candidate; not imposed: per-row dualisation).
**Measured** (four single-coupling tests at z*, R = 19/50, gap `V − π = 0.047188`):

| coupling imposed alone | gain ≤ |
|---|---|
| sector-chain radius sharing (cycle DP) | 1.8e-5 |
| cyclic closure `b = b^cl` | 4.2e-4 |
| holonomy of the side-matching system | 3.4e-5 |
| 11 site angle sums / fan angular resource | 5.3e-3 (11 % of gap) |

⇒ no single coupling tested recovers more than 12 % of the gap; the gap is diffuse over the 29
factors (faces 0.0263, rings 0.0158, switches 0.0051).
Falsifier: a coupling C with `V_C(z*) ≤ V(z*) − 1e-2`, or some `z` of the family with
`V(z) − π < 1e-3` at R = 19/50.

## Next executable obligation

(1) Cheap leg: impose the holonomy conditions, eliminate the 20 log-radii along a spanning tree
of the 20-node face/switch graph (root `γ_0 = 1`), **re-optimise `z`** on the tightened family
(reuse `lead/q0_closure_dual.py`'s LP/separation machinery) and compare with `V(z*) = 3.18878`
at R = 19/50. (2) Structural leg: the inverse problem — find `z` making the candidate's tuple
simultaneously maximal in all 29 factors (≈70 stationarity rows + global-maximality conditions).
At `R = r*` a genuine cover exists, so every valid relaxation has `V(z) ≥ π`; sharpness requires
`V(z) = π` exactly. If that system is inconsistent, the factor family is structurally incapable
of the sharp bound and the work must switch representation (C839 62-variable shape model with the
2 cycle + 6 circle rows) instead of adding further couplings.

## Degenerate reading (do not re-derive)

`lead/joint_nested_frozen.json` is **not** usable as a pure 29-factor dual (its 7-atom block is
joint by construction): independent 29-factor maximisation gives total **57.64** at R=19/50.

Full detail, tables, scope guards: `REPORT.md`. Repro: `r20_factor_probe.py`,
`r20_candidate_calibration.py`, `r20_residuals.py`, `r20_mechanism.py`,
`r20_closure_coupling.py`, `r20_gap_decomposition.py`, `r20_holonomy.py`.

---

# R20-TC-IV3 revision (2026-09-25 20:18) — margin fix + 5 outer distance bounds

**Grade: `proved-interval` (ONE box, local root only; no covering radius, no optimality).**
Evidence: `r20_tc_iv3.json` (hash-pinned to the current `r20_tc_iv3.py`), `r20_tc_iv3.log`,
repro `py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv3.py` (same box, same `Y`,
same dps 40/30/25 as the certified run — no precision escalation, no box change).

### (1) Margin definition corrected; withdrawn formula quantified

* Definition is now `margins[i] = min(rad + lo, rad - hi)` on `K_i - c_i = [lo, hi]`, an exact
  rational; the withdrawn formula was `min(rad - lo, rad - hi)`.
* `slack_min = 9.9566757e-10` — **identical** to the withdrawn reading (99.57 % of the radius);
  the withdrawn formula's per-coordinate overestimate is at most **3.486e-17** (relative to a
  ~1e-9 slack), i.e. it was a report bug only, and no coordinate's sign changes.
* New self-check passes for all 12 coordinates: `margins[i] > 0  ⟺  inclusion holds on i`.
* Certificate readings are bit-identical to the pre-fix run: `Q = 0.004332416836240972`
  (exact rational), `max|K-c| = 4.3324275e-12`, `inclusion = True`, dps 40/30/25 identical.

### (2) The five OUTER DISTANCE radicands are now verified C¹-domain items

Rule (valid unconditionally, since a square is non-negative): a component interval that excludes 0
contributes `(min|endpoint|)²`; a component straddling 0 contributes 0; a row is inconclusive only
if **both** contribute 0. Strict rational `dist²` lower bounds:

| row | `dist² ≥` |
|---|---|
| corner (k=1,l=1) | 0.14438772131016 |
| corner (k=2,l=0) | 0.14438771384328 |
| corner (k=3,l=0) | 0.14438765239459 |
| corner (k=8,l=1) | 0.14438771771568 |
| waist (C₆, m, h) | 0.14438772446269 |

`min = 0.14438765239459` (≈ `R² − O(1e-9)`, matching the lead's independent
`lead/tc_root_geometry.json` reading `> 0.14`). Row `corner(k=8,l=1)` reports `dy ≡ [0,0]`: this is
**symbolic cancellation, not precision** — `θ_8 = π − a₀`, `a₈ = a₀`, hence `θ_8 + a₈ = π` and
`e₈ = (−1,0)`, while `U_8^y = (ρ₈ − ρ₀) sin a₀ = 0` because `ρ₈ = ρ₀` (reflected `a`-list); so that
row's `dist² = dx²` exactly.

### (3) Withdrawn intermediate reading (recorded, not hidden)

The first patched run (20:15) used an over-conservative outer rule ("both components must exclude
0") and therefore self-judged `outer_distance_positive = False`, `verdict = False` for row
`k=8`. That self-judgement is **withdrawn**: it was an implementation slip in the *new* check only
(the certificate numbers were bit-identical), and it is not a certificate failure. The corrected
rule above gives `outer_distance_positive = True` and `verdict = True`.

### (4) C891 independent review event

`claim_review(id=C891, verdict=reviewed)` was executed by this executor
(reviewer `881f698d-857f-4583-b535-2ee3fd675a23` ≠ producer `session-f61549f0...`), with evidence
`r20_tc_iv3.json/.log + lead/TC-ROOT-SOURCE-IDENTITY.md + lead/tc_root_geometry.json` and control
"own interval tree-walk engine + corrected margins + 5 outer bounds". Independently reproduced:
`Q = 0.004332416836240972 < 1` (own `J(U)`, 0.91 % tighter than the lead route whose value
0.00437197162 is reproduced through my exact-rational pipeline), strict inclusion 12/12
coordinates, identical at dps 40/30/25, `slack_pos_iff_inside = True`, the five outer bounds above,
and the `k=8` symbolic-zero explanation. No new claim registered. Res5 source-level identity is
covered by the lead's assignment-level analytic proof (`lead/TC-ROOT-SOURCE-IDENTITY.md`); it was
**not** re-proved by CAS here (A is closed).

---

# R20-TC-GERM (D, 2026-09-25) — explicit-inverse rank certificates, SVD-rank reasoning withdrawn

**Grade: `proved-interval`.** Evidence `r20_tc_germ.py`, `r20_tc_germ.json`, `r20_tc_germ.log`
(repro `py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_germ.py`, ≈8 s). Registered
by the lead as **C899** (pending).

* The withdrawn reasoning ("rank 5 / rank 35 from numerical singular values ⇒ germ") is deleted
  from `POLY-BRANCH-EQUIV.md` §2 corollary and §3's rank row; σ values are now labelled
  **diagnostic, non-bearing**.
* Analytic side: explicit `W_A` (5×5, columns `[0,1,2,3,6]` kept by QR-with-pivoting on the point
  Jacobian; recorded to 17 digits) with `q_A = ‖I₅ − W_A M(U)‖_∞ = 1.087921746e-5 < 1` on the
  same 1e-9 box ⇒ the 5×7 Jacobian has rank 5 on the box ⇒ `{res5 = 0}` is locally a smooth
  2-manifold. Point-level reading `q_A = 1.245e-15`.
* Algebraic side: explicit `W_B` (35×35; pivoting drops `y₁, y₀`) with
  `q_B = ‖I₃₅ − W_B J_alg‖_∞ = 5.7122086e-6 < 1` on the image of the **full** 1e-9 box (first of
  three attempted levels) ⇒ `J_alg` has rank 35 there ⇒ the algebraic zero set is locally a
  smooth 2-manifold. Point-level `q_B = 1.450e-14`.
* Germ: two smooth 2-manifolds + the mutually inverse maps F/B on branch (B) ⇒ the germs
  correspond. Scope: local, one box; no global component count, no covering radius, no optimality.

# R20-TC-ELIM2 (E, 2026-09-25) — symmetric active family, finite branch

**Grade: `numeric`/`structural` (symbolic identities are exact; root readings are `numeric`;
no claim registered).** Evidence `r20_tc_elim2.py/.json/.log`, `TC-FAMILY-ELIMINATION.md`.

* **Caliber**: symmetric active family (mirror symmetry + 5 active tight rows + boundary
  saturation), **finite branch** only. "Whole ring domain" and "moving rings" wording withdrawn.
* **E0a** chain identity: `U_k − C_k = C_{k+1} − e_k`, `|U_k−C_k| = |U_k−C_{k+1}| = R` from
  `ρ² − 2ρcos a + 1 = R²`; symbolic → 0; numeric per-row ≤ `1.9e-61`; `Im U_8 = −1.1e-61`,
  `Im C_4 = 0`.
* **E0b** analytic eliminations that are VALID (verified symbolically with generic data → 0):
  `y0 = 2ReU_3 − ρ_4` (other root `y0 = ρ_4`), `y1 = ReU_8 + R` (other `−R`); `h` stays derived from
  `h² = R² − d²`, and the waist row may be **rewritten** (not eliminated) as
  `h = [((y0+y1)/2−ReC_6)²+(ImC_6)²−d²]/(2 ImC_6)`.
  **WITHDRAWN (corrected 20:36):** claiming `R = −[(ReU_8−ReU_1)²+(ImU_1)²]/(2(ReU_8−ReU_1))`
  as an *explicit* function of the angles is FALSE — `ReU_8, ReU_1, ImU_1` depend on `R` through
  `T_k = √(R²−sin²a_k)`. It is a fixed-point rearrangement:
  `φ(R*) − R* = 6.4e-17` but `φ(R*±1e-3) − (R*±1e-3) = ∓4.5e-3`
  (`r20_tc_r_dependency.py/.json/.log`). Valid root readings: `y0 4.58e-16`, `y1 6.86e-18`,
  `h −5.34e-17`; denominators `−0.41304592`, `0.69442412` safely non-zero.
* **E1 (corrected count)** after eliminating `y0, y1` the content is **THREE equations in FIVE
  unknowns `(a0..a3, R)`**: `E1 = (y1−ReU_1)²+(ImU_1)²−R²`, `E2 = (y0−ReU_2)²+(ImU_2)²−R²`,
  `E3 = (m−ReC_6)²+(h−ImC_6)²−R²` (residuals at the certified centre `5.26e-17 / 2.01e-18 /
  1.35e-16`). `R` remains an unknown: `∂ρ_k/∂R = −R/T_k ∈ [−11.49, −1.46]`,
  `∂ReU_1/∂R = +0.784`, `T_k = 0.1107…0.0331` ⇒ the dependence is load-bearing.
  `F_c` concyclic form (**C894 was RETRACTED** — cite the corrected alternative source, never C894
  as proved-exact; C896 is `numeric` only, not an exact filter): `F_c(C_2,C_3,H0) = −6.4e-18`,
  `F_c(H0,H1,C_6) = −5.7e-18`. Branch table: the two "other" branches give `|H0| = 0.8925`
  (`y0 = ρ_4`, i.e. `H0 = C_4`) and `|H1| = 0.9094` (`y1 = ReU_8 − R`), both `> 1−R = 0.6200`
  ⇒ **infeasible** (not strictly inner); the certified branches give `H0 = +0.27298`,
  `H1 = −0.14943` (signed; both feasible).
* **E2** leverage (corrected): `∃ tight config with R < r*` inside this branch ⟺ `∃ (a, R)` in the
  domain with `E1 = E2 = E3 = 0` and `R < r*` — a **5-variable** feasibility problem with `R`
  implicit (no explicit-`R` shortcut, no angle-only form). Threshold = finite Lagrange system
  `e_R = Σ_{i≤3} λ_i ∇E_i` together with the three rows: **8 equations / 8 unknowns
  `(a0..a3, R, λ1..λ3)`** — finite, no resultant. Decidability scheme (proposed, **not executed**):
  explicit-inverse (Neumann) rank certificate for the 3×5 Jacobian, same style as C899, plus
  certified enclosure propagation along the family (C891/C899 machinery); no sampling.
  **Verdict (b)** for the univariate
  `q(R)` target, with the explosion-point spec (19 vars / 17 eqs / degrees `[2,6,8,10,14,18]` /
  largest 23 210 ops) and the required representation change recorded.
* **Germ arithmetic audit (this round, no new claim)** — `r20_tc_germ_arith.py/.json/.log`:
  the recorded `W_A` matches an independently recomputed inverse to float64 rounding (max entry
  diff 2.2e-16), reproduces the point contraction (`8.2e-16` vs recorded `1.2e-15`) and a
  2⁷-corner sweep stays below `q_A` (`1.85e-6 ≤ 1.088e-5`). **`W_B` is missing from
  `r20_tc_germ.json`**; an independent recomputation of the same 35×35 subblock gives a float64
  contraction of `5.5e-16` instead of the recorded `1.45e-14` (both ≪ 1: inequality corroborated,
  value not bit-reproduced); the recomputed `W_B` is stored in `r20_tc_germ_W_B.json`.
* The earlier `r20_tc_elim.py` (7-unknown probe + resultant/Groebner sketch) is **superseded and
  was not run**; the 8D resultant is not enlarged. The `6.9e-16` augmented-singular-value
  "rank ⇔ KKT" reading is **numeric diagnostic only**, not evidence (an exact rank deficiency is
  not proved by a small numerical singular value, and the KKT equivalence would need the 3×5
  full-row-rank as a separate hypothesis). Own diagnostic reproduction (reduced concyclic
  variables): `F1 = −8.94e-18`, `F2 = −4.00e-19`, `F3 = −2.12e-17`; 3×5 singular values
  `[1.8998, 1.0971, 0.2644]`; 4×5 augmented `[2.1061, 1.1633, 0.3064, 5.03e-16]`. No new claim.

---

# R20-FIXED-U-REACHABILITY (audit for r20-geometry's fixed-U uniqueness lemma, 2026-09-25 late)

**Grade: exact combinatorial audit on numeric dual data; no claim registered.**
Evidence: `r20_fixed_u_reachability.py`, `r20_fixed_u_reachability.out.txt`,
`r20_fixed_u_sweep.json`, `r20_fixed_u_dual_export.json`; input read-only
`r20-alternative/socp_anchor_export.json` (SOCP oracle of `lead/FIXED-SWITCH-SOC-REDUCTION.md` §2).

* The oracle object actually present has **51 constraints** (18 endpoint `|c_i−U_k| ≤ t` +
  33 face-incidence `|c_s−z_f| ≤ t`), `Σα = 1 + 1.3e-14`, `V = 0.3799838531198385`,
  `V − R* = −2.2e-16`. The lemma's "(H1) all 45 edges" does not match it: the export has 51 edges,
  **40 with `α > 0`** and **11 with `α = 0` exactly**, so (H1) as literally stated fails.
* **Combinatorial precondition (all sites anchored) HOLDS on the raw data**: with G⁺ = {α > 0},
  the exported 22-node graph (11 sites `c0..c10`, 11 aux `z0..z10`, 9 anchors `U0..U8`) is
  **connected** ⇒ unpinned sites = none. My independent BFS/union-find reproduces the calibrated
  self-tests (path instance: only the slack node unpinned; anchor-free cycle: correctly flagged),
  so the check is discriminating.
* **Important caveat — the anchoring is numerically fragile.** 19 of the 40 positive α's are
  `< 1e-12` (smallest `5.551e-17 = 2⁻⁵⁴`, a rounding residue; total `5.34e-13`); only 21 edges have
  `α ≥ 1e-3`. Threshold sweep (keep only `α ≥ τ`): `τ = 0 / 1e-16` anchored; **`τ = 1e-14`
  ⇒ sites `c1, c10` unpinned**; **`τ ≥ 1e-12` ⇒ `c1, c2, c3, c9, c10` unpinned**. So the pinning of
  the four low-α ring sites and both hubs rests entirely on 1e-15-level multipliers. The
  *combinatorial* conclusion is fine as a statement about the supplied floats, but (H1)'s
  strictness-with-margin and Corollary 3's "strict positivity persists in a neighbourhood" are
  **not supported by this data**; a certified dual with margins (or pinning those sites by exact
  geometry/active-set reasoning) is needed before the lemma carries a local uniqueness claim.
* I did **not** run `r20-geometry/fixed_u_primal_uniqueness.py` (it writes its `.out.txt` into that
  directory, outside my write scope). `r20_fixed_u_dual_export.json` is in the schema it expects
  (`anchors`/`nodes`/`edges`; hubs named `c9`/`c10` so its `startswith("c")` site-test covers all
  eleven sites) for their own calibrated run.
* **UPDATE (aligned to C909).** The "reading vs theorem" caveat above is closed upstream:
  `lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` §2 supplies the **exact** vector-force certificate
  (C897 `μ_i>0`, `ν_f>0`, sum exactly 1; all 45 carrying edges of length `R*`; zero tangential and
  strictly positive radial anchor loads; dual work `= R*` ⇒ `V(U*) = R*`), §3 pins **all 11 site
  coordinates** at fixed `U*`, `t ≤ R*` (the two slack auxiliaries non-unique, immaterial), and §4 is
  the stronger statement: for every site neighbourhood `O` of `C*` there is an anchor neighbourhood
  `N` of `U*` such that **every** oracle-feasible solution at `U ∈ N`, `t ≤ R*`, has sites in `O`.
  So this lane's 40/11 + tiny-α readings are demoted to **consistency cross-checks**, and
  `r20-geometry/FIXED-U-PRIMAL-UNIQUENESS-LEMMA.md` now states Lemma 1/Cor 2/Cor 3 as *conditional on
  C909's exact force certificate* (geometry lane's own wording, H9 there).

# R20-GRAPH/LOCAL-INTERFACE AUDITS (2026-09-25 late; all read-only, no claims registered)

**Grade: independent audits + analytic lemmas; every statement conditional-scoped as written.**

| artifact | object | key content |
|---|---|---|
| `CENTRAL-SCREEN-INDEPENDENT-AUDIT.md` | alternative lane's central-crescent screen | pinned final sha `dcffaf17…`/`22a78b34…`; five items pass; my own rational-interval kernel (`r23_central_screen_audit.py/.json`) reproduces the declared values to 12 digits (`G` face 0 `0.0245686655427838664`, face 4 `0.0245401216821034308`; `ε_B ≤ 0.067372319`, `ε_A ≤ 0.061717335`; nominal `G = 0.1541589819`, `ε_B = 0.0330620706687`, chord bound `0.378542769`); branch/guard evidence recorded |
| `C900-INDEPENDENT-CHECK.md` + `c900_independent_check.py/.json` | C900 conditional fiber elimination | bearing-interface pass; own enumeration `35 = 10 old + 25 new = 12+4+8+1`; MEC criterion 12/12; strict-min lemma 4/4; (E) premise instantiated on the audited box only |
| `INTERFACE-DEGENERACY-CHECK.md`, `GRAPH-INTERFACE-CHECK.md`, `STRAIGHT-SITE-EMBEDDING-PROOF.md` | q0/q1 classification interfaces | separate embedding proof (simplicial closed disk → uniform triangulation → subcomplex of one planar Delaunay triangulation → injective → compact/Hausdorff embedding → Jordan ⇒ hubs strictly inside, `P` simple, no holes/exterior triangles); my earlier "false `Rc ≤ r`" objection **withdrawn as out of domain** (Voronoi vertex = equidistant ⇒ empty-circle radius ⇒ circumradius `≤ r`); "no degeneracy leak" restated as: metric exclusions relaxations (no leak) vs class enumeration conditional on (P1)–(P3) |
| `LOCAL-PRIMAL-TO-COVER-TRANSFER.md` | local primal ⇒ cover | L1 no-hole, L2 endpoint ⇒ whole owned arc (no "inward" needed), L3 acute ⇒ MEC=Rc — independent re-derivations of lead §5's three ingredients; **superseded in status by C910**, kept as independent evidence; conditional on **C909 + C902**; 20 free nodes (11 sites + 9 active aux; 2 slack aux isolated) |
| `SECTOR-RELAXATION-DUAL-EQUALITY.md` | per-box lower bounds | repaired after lead review: keep the **joint** `U_i` (per-edge projection is equivalent, the **conjunction** is not — two balls can each meet the sector with empty common intersection); dual budget is the norm **ball** (`≤1`, not the sphere); **singleton arcs use Sion, not strict-interior Slater**; major arcs (`<2π`) give a **disk cap**, only the full circle gives the disk; **no hidden loss**: sector minimum = arc minimum ⇒ relaxation = fixed-force angle-min; §4 pilot B&B proposal (deficit-simplex decomposition of `P`, proposal only, not implemented) |
| `socp_fixed_switch_check.py/.json`, `tie_derivative_identity.py`, `q0_67_orbit_check.py`, `straight_site_control.py` | oracle/symmetry numerics | 9 switches **all tight** (`ρ_i = r`); 11 faces **all acute**, **9/11 tight** (7 fan + 2 central, matching C897), slack fan faces `(5,6,9)`, `(7,8,9)` with slack `1.153e-3`; hub degrees `(7,6)`, `E = 21`; tie derivative **exact**: `∇_c ρ = A·u`, `A = ⟨U−c',t⟩/⟨c'−c,t⟩`, `B = ⟨U−c,t⟩/⟨c−c',t⟩`, `A+B = −1`, split `(α,1−α) = (−A,−B)` (**never ½/½**; asymmetric samples `α ∈ {0.206,0.307,0.416,0.449,0.520,0.570}`), matching lead §5's `α = s_d/(s_d−s_c)`; the q0(6,7) placements form **one orbit** under `D_9 × hub-exchange` (18 configurations, canonical rep `u=0,v=4`, matching the saved candidate's faces `(0,9,10)`, `(4,9,10)`) |

**Withdrawn in this block (do not resurrect).** (i) "the free-site min-r dual degenerates to 0" — a
site carries two endpoint constraints at *distinct* switches, `inf_c(‖c−U‖+‖c−V‖)/2 = ‖U−V‖/2 > 0`;
(ii) "half-half split" for the tie weight; (iii) "`|p_out| = 1` exactly at the nominal rational data"
— it is exact only in the exact chart; at the saved `1e17`-scaled rationals `|p_out| − 1 ∈
[+2.2e−17, +4.7e−17]`; (iv) "finite dual fields can certify sharpness near `U*`" only on a small
punctured neighbourhood, and only for non-attaining fields (local continuity); (v) my proposed
"`V ≤ R* − c‖δθ‖²` local theorem" — the dual gives `V ≥ bound` only, the direction was backwards.

**Residual obligation in this lane.** (I10) the global bound on `P ∖ 𝒩` for the fixed-switch oracle
(`min_P V ≥ R*`), for which the convex sector relaxation + per-box bounds are the tool (pilot B&B
proposed, not implemented); optional quantitative upgrade of the local statement to an explicit
`δ₁`/`𝒩`. Upstream registered results used here: C891/C892 (exact root and its cover; `R*` = the
exact-root radius, **not** the C249 45-digit print, **not** the C529 rational), C897 (KKT lift),
C902 (physical strict local), **C909/C910** (exact sharpness + local transfer).

---

# EXACT-AREA-ASSEMBLY-AUDIT (shared-factor area identity; lead's direct obligation)

**Grade: analytic derivation (exact algebra), audit level; no claim registered.**
Deliverable: `EXACT-AREA-ASSEMBLY-AUDIT.md` (this directory only); internal localisation script
`r20_area_localize.py`. Read-only audited sources: `lead/SHARED-FACTOR-DUAL.md`
§"Exact area alternative", `lead/BOUNDARY-SWITCH-ANGLE-PROOF.md` §1/§3/§4. Closed `b`-direction
not re-audited; no numeric calibration substituted for the identity.

* **Verdict: the identity `pi = Σ_faces 2ρ²∏sin + Σ_switches σ²sin(2b)/2 + Σ_rings caps` is a
  genuine consequence of the CLIPPED VORONOI partition + co-circular refinement.** Derivation
  chain (all exact): (A) clipped nearest-site cells partition `D` (distinct sites; hubs own no
  boundary arc since `|x−hub| ≥ 1−|hub| ≥ r ≥ |x−ring site|`); (B) per-cell fan decomposition with
  the apex at the *site* (directed-area lemma for a convex cell with one circular arc, giving
  `(1/2)σ_Lσ_R sin α + (w − sin w)/2`); (C) pairing across shared Voronoi edges gives
  `(|c_i−c_j|/2)|e|`; (D1) the circumcenter projects to the side midpoint; (D2) interior edges pair
  into `d²/4(cotθ+cotθ')` with `cotθ+cotθ' = sin(θ+θ')/(sinθ sinθ') ≥ 0` **by Delaunay only**;
  (D3) boundary-adjacent (ring-ring) edges satisfy the crux identity
  `a|zU_i| = (d²/4)cotθ + σ_i²sin(2b_i)/2` (under `ℓ+ρcosθ ≥ 0` = §1's `t < ℓ`);
  (D4) `(1/4)d²cotθ = (ρ²/2)sin2θ`, so `(1/4)Σ d²cot = (ρ²/2)Σ sin2 = 2ρ²∏sin = area`.
* **Caliber (lead audit applied): the obligation covers the q1 and q0 exclusions, not only the
  canonical (6,7) configuration; no global hull / convex-position / Delaunay-global assumption is
  used** — everything is phrased on the *clipped refined dual disk* (interior face list + boundary
  structure), Voronoi vertices outside `D` are allowed, and (D2)/(D3) are local signed-offset
  identities (two incident faces / one face + a switch). The earlier "hull edge" wording is
  replaced throughout.
* **No straight-site-triangulation assumption is used**: circumcenters never appear as tiling
  vertices (only in the *signed*-piece identity (D4), whose sum is sign-independent, and in (D1)).
  **Obtuse faces** are covered by (D4) (`cot < 0` terms) and by the sign condition of (D3), which
  is `t < ℓ` — exactly `BOUNDARY-SWITCH-ANGLE-PROOF.md` §1, proved without acuteness.
  **Artificial (co-circular) edges**: their *area* content is exactly `0` (`cotθ+cotθ' = 0`, the
  two circumcenters coincide so the dual Voronoi edge has zero length) — corrected wording: this
  says nothing about the `ρ²sin²θ` atom, which uses the face's *opposite angle* and stays positive;
  such an edge is a genuine shared-side constraint of positive primal length.
* **Withdrawn/incorrect statements in the first version of this audit (lead audit, all fixed in
  the file)**: (1) `(1/4)d²cot = ρ²sin2θ` → correct is `(ρ²/2)sin2θ`; (2) "Delaunay ⟹ the two
  circumcenters are not on the same side" → wrong (obtuse case can put them on the same side);
  only the *signed sum* is nonnegative; (3) "the `ρ²sin²θ` atom vanishes on a cocircular edge" →
  wrong, deleted (shared-side atom vs area content); (4) H2 must be quoted **non-strict** (closed
  half-plane) — the equality case `α = π` is a legal degeneration and the cap formula still holds.
* **Residual points (presentation-level only; the sources' main proof is correct and this audit is
  not an independent theorem)**: (i) the derivation needs each site in the **closed** inner
  half-plane of every chord — this follows from inward-rootness (`|c| ≤ √(1−r²) ≤ cos(w/2)`) and
  **has since been added to `BOUNDARY-SWITCH-ANGLE-PROOF.md` §4** by the lead, so the earlier
  "stated in neither source document" remark is withdrawn; (ii) the identification "the inside-`D`
  bisector exits `∂D` at the switch, and its other end is a primal vertex of the selected clipped
  dual disk hence **in `int D`**" (there are no two-switch edges) is used implicitly and is part of
  the reduction's choice of clipped dual disk; (iii) H4 (`t < ℓ`) is the load-bearing sign
  condition for the boundary-adjacent edges, proved in §1 of that document; (iv) the identity
  concerns *genuine* configurations — the certificate's relaxed (zero-radius / zero-angle) domains
  merely enlarge the range and must not be read as extending it.
* **Textual corrections applied after the lead's second read** (all in the audit file): face list =
  the 11 refined triangles *whatever they are* (q1 leagues include the **ear** triangle; no longer
  "hub-fans + 2 central"); H3/§6/D3 no longer say the boundary edge's other end may lie outside
  `D` — the selected dual disk's primal vertices are in `int D`, so `[z,U]` is untruncated and only
  *unselected* global vertices are unrestricted; §3 lemma is **closed**-half-plane with the
  `p ∈ [P,Q]` (`∠PpQ = π`) flattening case; an `alpha = pi` **ring** cell still has its arc (only a
  **hub** cell has none).
* Non-bearing consistency (labelled as such in §7 of the audit): at the oracle configuration
  `Σfaces+Σswitch+Σsector+Σsegment = 3.141592653589793 = π` with difference `0.0e+00`; per-face
  `2ρ²∏sin` vs `area` ≤ `1.1e-16`; crux identity (D3) edgewise residual ≤ `5.6e-17` on all 9 ring
  edges. These check the bookkeeping only; the proof is the derivation above.
