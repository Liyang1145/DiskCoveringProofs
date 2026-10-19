# Class line (class33/) — status 2026-10-15 (Asia/Shanghai)

**Nothing in this section is paid.** No Mathlib/WIP-toolchain build ran in this sandbox (the class line
does not own the Mathlib process; the build line's v4.33.1 toolchain was lost in a container restart at
~14:03 CST). Everything below is either (a) core-Lean **pre-validation** compiled with the v4.33.1 *core*
toolchain (Init only, no Mathlib), (b) exact-`Fraction` Python **pre-validation**, or (c) WIP-style Mathlib
**DRAFT** source (59 modules, 0 sorry) (uncompiled) for the build line to gate.

## 1. Route choice: route 2 (SevenFiniteTables), not route 1 (Canonical33Obligation)

* Route 1 `ActualMainRoute.Canonical33Obligation` quantifies over every representative cover and asks for a
  cyclic cut, a hub permutation and 11 witness points within `r` of all three face sites — i.e. the
  C923 nearest-site / clipped-Voronoi / dual-disk topology (§§1–6). No Mathlib support; months.
* Route 2 `CanonicalSharedMomentFiniteCertificate.full_disk_bound_of_finite_class_tables h450 henergy T`
  needs only finite rational data + interval trees: for each class a `CanonicalCoeffQ`, `kap`, `eta` and a
  `FiniteCanonicalCertificate` = balance + signs + 11 face trees + 9 switch trees + 9 sector trees + one
  strict rational total `< piLo`. With the proved 8→2 orbit transport
  (`CanonicalBalancedFiniteClassCertificate.SixAndBalancedFiniteTables`) the count is
  3 (Q0 m=1,2,3) + 3×8 (Q1 m=1,2,3, all cuts) + 2 (Q1 balanced representatives k=7,1) = **29 certificates**.
  Every remaining step is mechanical given proposals. **Route 2 chosen.**

## 2. Key finding: the A25 "refutation" of the concrete batches was a labelling error

The A25 lead record (C1804/C1806/C1811/C1812) tested `start0_face1`/`start0_switch*` against **`q0Faces 1` with
identity labels** and correctly found them incompatible — but those data are the historical **balanced-Q1
start0** proposal (`cover11/.../lead/shared_moment_dense_certificate_0_4.json`), whose labels are
ear (0,1,2), core [0,2,…,8]. Relabelling ring h ↦ h−1 (mod 9), hubs fixed:

* historical start0 ↦ Lean **`q1Faces 7 4`** and start2 ↦ **`q1Faces 1 4`** — exactly the two
  representatives of `BalancedTwoFiniteTables` (checked by recomputing `q1Faces` from the Lean definitions).
* All nine batch tuples are **exactly** `canonicalSwitch{P,Q,B,D2,D1}` of the instantiated rep7 table at
  Lean index **j = K−1 (mod 9)** (45 exact rational identities).
* `start0_face1_{p,q,b}` = canonical coefficients of rep7 face {1,8,9} with slots reversed
  (canonical slot s = data slot 2−s); the proved `start0_face1_full_domain_upper` therefore bounds that face
  via `SharedMomentFactorPermutation.face_upper_of_permuted_coefficients`.

So G1/G2 are closable and the 7,923 switch nodes + 1,239 Face1 nodes are **on** the critical path.

## 3. Nine-switch aggregation (G1) and bridge (G2)

* The "qualify 1/2000 vs 141/1e6" step is unnecessary: `canonicalTotalUpperQ` takes per-switch maxima
  additively. `rep7SwitchMax j := start0_switch{j+1 mod 9}_bound`; Σ = **22523/250000 exactly**
  (= `start0_switch_total_bound`). Switches K=4,5,8 simply contribute 51029/1e6, 4839/2e5, 14023/1e6.
  `SharedMomentConcreteLeafControls.start0_switch0_bound = 1/2000` is a different-namespace control (G4);
  the bridge never opens it.
* Structure bridge: `certificate_mono` + `switchCertificate_of_direct` (direct leaf ↦ `GradientSwitchLeaf`
  via `Or.inl (Or.inr (Or.inl h))`; root `switchCell 0 (1571/1000)` contains `switchRoot` since
  piHi/2 ≤ 1571/1000).
* Budget with these maxima (rep7): sharp constant −3.464894…, faces 3.440353 (hist uppers ↑1e-6),
  switches 0.090092, sectors 3.070858 → total 3.136409 < piLo, **slack 0.00518**.

## 4. Instantiated tables (pre-validated)

| table | Lean class | source | balance | graph | strict with proposed maxima |
|---|---|---|---|---|---|
| rep7 | `q1Faces 7 4` (balanced rep) | dense_certificate_0_4 (σ: h↦h−1) | ✓ | ✓ | slack 0.00518 |
| rep1 | `q1Faces 1 4` (balanced rep) | dense_certificate_2_4 (σ) | ✓ | ✓ | slack 0.00176 (tight) |
| q0m2 | `q0Faces 2` = `q0_degree4` (hub degrees 4,9) | q0_moment_dual_certificate_0_2 (identity, eta=0) | ✓ | ✓ | slack 0.163 |

All three: kap ≥ 0, eta ≥ 0, exact sharp constant computed; Python cross-check against the historical
generator formulas; core-Lean `Class33Core.{Rep7,Rep1,Q0M2}` + `Audit` compiled, **34/34 `#print axioms`
⊆ {propext, Classical.choice, Quot.sound}**, with negative controls (flipped mask unbalanced, wrong cut /
wrong m rejected, unshifted switch index mismatches, inflated maxima break strict).

## 5. Trees generated (exact leaf kernels transcribed from WIP, validated on Lean-green leaves)

Kernels: `py/switch_kernel.py` (switchDirectUpperQ) — positive control 3,966/3,966 SwitchBatch accept leaves
pass, tiling ✓, M−1e-3 rejects; `py/face_kernel.py` (planeDirectUpperQ, PlaneOutside, planeGradientUpperQ) —
80 direct + 21 outside + 519 gradient Face1 leaves all pass.

| item | trees | leaves | status |
|---|---|---|---|
| rep7 switches | 9 (A25 batch) | 3,966 | Lean-green (A25); bridge DRAFT |
| rep7 face {1,8,9} | A25 Face1 | 620 | Lean-green (A25); permutation bridge DRAFT |
| rep7 faces | 11 (M = hist+1e-4; {1,8,9} also = A25 Face1) | 10,349 | Python-exact |
| rep1 faces | 11 (M = hist+5e-5) | 11,585 | Python-exact |
| rep1 switches | 9 | 8,008 | Python-exact all; core-Lean all 9 compiled (S2..S8 on 2026-10-15 14:44, 100-leaf parts) |
| q0m2 switches | 9 (M = hist+0.002) | 795 | Python-exact; core-Lean all 9 compiled (2026-10-15) |
| q0m2 faces | 11 (M = hist+0.004, gradient leaves) | 4,867 | Python-exact |
| sectors (all tables) | 0 | — | **not started**: needs transcription of `MetricSectorLocalGradientCertificate.PositiveCertificate` + NodeBounds witnesses |

Actual budgets with the generated face/switch maxima (room left for the 9 sector maxima vs historical sector sum):
q0m2 room 1.425498 vs 1.324628 → **0.0112 per sector**; rep7 room 3.074942 vs 3.070853 → **4.5e-4 per sector**;
rep1 room 5.526456 vs 5.525418 → **1.15e-4 per sector** (tight). (data/*_budget_actual.json)

## 6. DRAFT Mathlib modules (class33/lean/N11Formalization/, uncompiled)

`Class33Labels` (canonicalLabel lemmas, A25 C1812 technique) · `Class33RepData` (rep7D/rep1D/q0m2D,
`*_balance` via `sum_slots` reindexing + ℤ `decide`, kap/eta signs) · `Class33SwitchBridge`
(certificate_mono, switchCertificate_of_direct, 9 batch SwitchCertificates, `rep7_switch_aggregate`,
45 identities, `rep7Switches`) · `Class33SwitchFields` + 18 `Class33SwitchTree{Rep1,Q0M2}S*` (batch-style trees)
· 33 `Class33FaceTree{Q0M2,Rep7,Rep1}F*` (Face1-style trees + `EfficientFaceCertificate`) ·
`Class33{Q0M2,Rep7,Rep1}Assembly` (`*Faces` fields; `q0m2_table_of_sectors : … → Q0FiniteTable 2`,
`rep7/rep1_table_of_sectors : … → RepresentativeFiniteTable 7/1`, i.e. each class reduced to 9 sector certificates + strict) · `Class33BalancedAssembly`
(`balanced_exclusion_of_two_canonical`, `rep7_certificate`, `rep7_face189_upper`).
No `sorry`. Expect compile iterations (simp/norm_num normal forms written without a compiler).

## 7. Inventory of the other classes (from historical docs; not verified)

* Q0 m=1 (3,10): historical DEGREE3-AREA-EXCLUSION (area argument, not shared-moment form) → needs a new
  canonical proposal (LP) before trees.
* Q0 m=3 (5,8): historical exclusion used C820 cyclic closure multipliers, which `FiniteCanonicalCertificate`
  cannot express → risk the canonical form is infeasible for this class; test by LP first.
* Q1 m=1 (3,9): area exclusion (DEGREE3); Q1 m=2: cluster-capacity + area (DEGREE4-TRIPLE, has eta);
  Q1 m=3 (5,7): shared-factor dual, starts 0–3 certified historically, start 7 by C815 — all need 8 cuts each
  in canonical form (no orbit reduction proved for m=1,2,3).

## 8. Next steps (class line)
1. Build line: gate the DRAFT modules (RepData → SwitchBridge → SwitchTrees/Fields → FaceTrees → Assemblies).
2. Transcribe the sector leaf (direct `sectorDirectUpperQ` with NodeBounds witnesses + gradient
   `PositiveCertificate`), validate on any Lean-green sector tree, generate q0m2 sectors (margin 0.011) →
   **first payable class `q0_degree4`**.
3. rep7 and rep1: 9 sectors each (margins 4.5e-4 and 1.15e-4 per sector); then `balanced_exclusion_of_two_canonical`/`BalancedTwoFiniteTables` pays q1_balanced.
4. Generate canonical LP proposals for Q0 m=1,3 and Q1 m=1,2,3 (24 cuts).
