# Lane B notes

## 2026-10-28 — stage-2 top aggregate + B13 draft (CI pending)

### Done
- Diagnosed why the recorded `Paid16GeneralNext1182` was absent: upstream
  `emit_aggregate_hier.py` uses `Path(o["path"]).stem` on Windows-style manifest
  paths. On Linux this preserves the backslashes and selects zero packet modules.
- Added lane-local deterministic emitter `n11-work/ops/lanes/B/emit_next1182_top.py`
  (sha256 `2381F7CE381CAEAFAA6FEA4E8835452468ADF4E3AF625E89A531703D7FCED031`).
  It reads the authoritative manifests, emits only the missing top module, and
  asserts both recorded character count and SHA256 before writing.
- Regenerated `N11Formalization/Paid16GeneralNext1182.lean`
  (sha256 `0EA12578B8541200A4AB803C4BFEFCF53D230A85F4345F8509A707B67A455E2F`,
  exactly the hash recorded in `Paid16GeneralNext1182-hier-manifest.json`).
- Read the actual emitted ID sets: `Paid16GeneralNext505.newIDs` has 505 ids in
  1160..2564; `Paid16GeneralNext1182.newIDs` has 1182 ids in 2565..5007.
- Drafted `N11Formalization/EnergyTerminalBatchB13.lean`
  (sha256 `6F31BCA53D4EA4461610E1415DFA60E846095C3333887E2A7FC63FB22A88E7B3`).
  It defines the 1997-id paid set, proves `paid_count` through
  `Finset.card_union_of_disjoint`, defines the 389-id residual, and proves
  `remaining_of_b13 : B13.RemainingTerminalRadius -> B12.RemainingTerminalRadius`.
  Disjointness is split into 16 bounded checks: B11 (310 ids) and Next505
  (505 ids), each against one of the eight <=168-id Next1182 sub-aggregates.
- Drafted `N11Formalization/EnergyTerminalBatchB13Main.lean`
  (sha256 `7685A0FFE7C192BC997EBD6FB5D17B96C197ABC72C42E43B319D9CA47655683C`)
  with `main_of_energy_b13_and_seven_classes` and the full-disk corollary.
- Registered CI targets in `n11-work/ops/lanes/B/TARGETS.txt`
  (sha256 `ADD6C300C665093237DB926701F44E16B02AED1B53C718C7B42496AFB7C4A956`):
  `Paid16GeneralNext1182`, `EnergyTerminalBatchB13`, `EnergyTerminalBatchB13Main`.
- **ROOT-IMPORT REQUEST:** after CI green, supervisor should import
  `N11Formalization.EnergyTerminalBatchB13Main` from the root instead of B12Main.

### Checks executed (scope stated)
- `python tools/project_status.py --check`: PASS, manifest declarations only; not
  a mathematical check and not a full byte audit.
- `emit_next1182_top.py`: PASS, exact byte-for-byte hash match to authoritative
  manifest for the top module. This checks regeneration bytes, not Lean elaboration.
- Static scan of B13 and B13Main: no `sorry`, `admit`, `axiom`, `native_decide`,
  `ofReduceBool`, `implemented_by`, or `maxHeartbeats 0`.
- No Lean build was run locally (project oleans absent; `lake env` attempted a
  Mathlib clone). All three targets are **CI pending**, not paid.

### Still unproved / risks
- `EnergyTerminalBatchB13Main` imports `C450ChainCompletionMain`, which is absent
  from this worktree. Its CI result is blocked on Lane A landing both C450 modules;
  do not diagnose a red B13Main as an energy-aggregate failure until those imports exist.
- `EnergyTerminalBatchB13.RemainingTerminalRadius` is an explicit unpaid premise
  over 389 terminal ids. It is not proved here.
- `ActualMetricClassReduction.SevenClassExclusions` remains unpaid.
- B13's 16 `decide +kernel` disjointness checks are unelaborated. If any is too
  heavy or fails, split Next505 into its 25 public literal `idsNN` sets and use
  `Finset.disjoint_union_left/right`; do not replace it with a global decide.

### Very next concrete step
Read the next `ops/ci/LATEST.md`. If B13 is red, fix the first kernel/elaboration
failure only and rerun the three targets. If green, ask supervisor to switch the
root import to `EnergyTerminalBatchB13Main`, then reconcile the residual count
against the 389-id census and preserve B12Main as a compatibility module.

## 2026-10-28 — implicit-binder defect fixed (CI still pending)

### Done
- Found a real elaboration defect in the previously generated top module and B13:
  `Finset.disjoint_left.mp h` returns `∀ ⦃a⦄, a ∈ s → a ∉ t`; the calls
  `(… ) a ha hb` supply `a` where a membership proof is expected. Minimal Lean
  probe `/tmp/imp_probe2.lean` confirmed the positional form errors, while
  `(… ) (a := a) ha hb` is accepted.
- Patched 8 occurrences in `Paid16GeneralNext1182.lean` and 16 in
  `EnergyTerminalBatchB13.lean`.
- Updated `n11-work/ops/lanes/B/emit_next1182_top.py` to reproduce the frozen
  upstream characters/hash before applying the fix. Provenance check passes:
  upstream 6389 chars / 6521 UTF-8 bytes,
  sha256 `0EA12578B8541200A4AB803C4BFEFCF53D230A85F4345F8509A707B67A455E2F`.
- New report `n11-work/ops/lanes/B/emit_next1182_top-report.json` records both
  upstream and corrected byte hashes; no frozen manifest was modified.
- **The earlier claim that the generated file exactly matches the manifest is
  superseded:** the manifest bytes contain this ill-typed pattern. The local
  corrected module is deliberately no longer byte-identical to that manifest.

### Current file hashes (UTF-8 bytes / sha256)
- `Paid16GeneralNext1182.lean`: 6577 /
  `5F6CB04F84D20AE127DE13498E6929BCE3E3C5BABFA751EF99BE630D0266CB17`
- `EnergyTerminalBatchB13.lean`: 7707 /
  `FCCD5FCE2C38569662F8AE904FFA4CB733BFDF64D7A0C31B129416EE3B8320DA`
- `EnergyTerminalBatchB13Main.lean`: 1441 /
  `7685A0FFE7C192BC997EBD6FB5D17B96C197ABC72C42E43B319D9CA47655683C`
- `emit_next1182_top.py`: 5450 /
  `9F2AD9813823B7B75D293F3843BE08E30368EC19059885CEAC2DB2A14A4BA0A5`

### Checks executed (scope stated)
- `python3 emit_next1182_top.py`: PASS for provenance reconstruction and
  deterministic rewrite; not Lean elaboration.
- Minimal Lean 4 core probe: PASS for the corrected implicit-argument form and
  FAIL as expected for the old positional form. Scope: generic binder pattern,
  not project modules/Mathlib Finset.
- Static declaration-aware scan of all three Lean modules: clean; the only
  `axiom` text is the permitted `#print axioms` diagnostics. No project Lean
  build (dependencies absent locally; full build prohibited on 2 cores).

### Still unproved / risks
- All three targets remain **CI pending**.  The 16 aggregate disjointness
  `decide +kernel` terms (B11/Next505 against eight Next1182 parts) are still
  unelaborated; Next505-vs-part has 505+168 literals, near/above the stated
  kernel threshold. If red, split Next505 via `new_mem` into its 25 `idsNN`
  pieces rather than introducing a global decide.
- B13Main remains blocked on Lane A's two missing C450 modules.
- `RemainingTerminalRadius` over 389 ids and `SevenClassExclusions` remain
  explicit unpaid premises.

### Very next concrete step
Wait for CI. If the top or B13 is red, address the first elaboration/kernel
failure only; first candidate is hierarchical Next505 disjointness via its 25
`idsNN` parts. Keep all non-CI statements labelled drafted/pending.

## 2026-10-28 — Next505/Next1182 disjointness range split (CI pending)

### Done
- Replaced B13's eight heavy `Disjoint Paid16GeneralNext505.newIDs
  Paid16GeneralNext1182Sxx.newIDs` kernel checks (505+up-to-168 literals each)
  with a numeric boundary proof. The authoritative literals satisfy
  `max Next505 id = 2564 < 2565 = min Next1182 id`.
- `next505_lt` dispatches `new_mem` to 25 `Finset.all` checks, one per
  `Paid16GeneralNext505.ids00..ids24` (21 literal ids each), proving
  `n.val < 2565` without quantifying over all 5011 `Fin` values.
- `s01_ge..s08_ge` are eight `Finset.all` checks (at most 168 literal ids each)
  proving `2565 ≤ n.val` for members of each Next1182 sub-aggregate. The
  second half of `new_disjoint_old` now closes each branch by `omega`.
- This avoids 200 cross-product checks and removes the only aggregate
  disjointness comparison above the measured kernel threshold.

### Files and hashes (UTF-8 bytes / sha256)
- `N11Formalization/EnergyTerminalBatchB13.lean`: 10348 /
  `B8334E3F516D86C6712DCC45FDE472509C0417B91438DCF0E6F2BF479BA340A3`
- `N11Formalization/Paid16GeneralNext1182.lean`: unchanged from prior entry,
  6577 / `5F6CB04F84D20AE127DE13498E6929BCE3E3C5BABFA751EF99BE630D0266CB17`
- `emit_next1182_top.py`: unchanged, 5450 /
  `9F2AD9813823B7B75D293F3843BE08E30368EC19059885CEAC2DB2A14A4BA0A5`
- `TARGETS.txt`: unchanged,
  `ADD6C300C665093237DB926701F44E16B02AED1B53C718C7B42496AFB7C4A956`

### Checks executed (scope stated)
- Independent source-literal extraction: parsed 25 Next505 `idsNN` definitions
  (505 unique entries, min 1160, max 2564) and 1182 S01..S08 `idsNN` entries
  (min 2565, max 5007); boundary assertion PASS. Scope: source text and lists,
  not Lean elaboration.
- Static hard-rule scan of B13 and Next1182: clean. `git diff --check`: clean.
- `ops/ci/LATEST.md` still says `no run yet`; **all three targets remain CI
  pending**, not paid. No project Lean build run locally.

### Still unproved / risks
- The 25+8 `decide +kernel` propositions and the `omega` branches are
  unelaborated until CI. B11-vs-S checks remain eight 310+168-literal checks
  (below the previously observed ~500-literal danger zone, but not proven safe).
- `EnergyTerminalBatchB13Main` still depends on Lane A's missing
  `C450ChainCompletionMain`.
- `RemainingTerminalRadius` over 389 ids and `SevenClassExclusions` remain
  explicit unpaid mathematical premises.

### Very next concrete step
Read CI. If green, send the root-import switch request for
`EnergyTerminalBatchB13Main` and preserve `B12Main`. If red, fix only the first
failure; if it is B11-vs-S, split B11 into its literal sub-aggregates by the
same range-membership pattern.

## 2026-10-28 — B11 range shortcut tested and rejected (CI pending)

### Done
- Tested replacing the eight B11-vs-Next1182 kernel disjointness checks with
  one proposed `b11_lt : ∀ n ∈ B11.paidIDs, n.val < 2565` range check plus
  `omega`. Source inspection disproved the premise: B01 includes 2166, B02
  includes 2162, B06 includes 3436, B07 includes 4179/4265, and B08 includes
  4267. B11 therefore straddles the 2565 boundary.
- Reverted the experiment completely. `EnergyTerminalBatchB13.lean` is restored
  byte-for-byte to 10348 bytes / sha256
  `B8334E3F516D86C6712DCC45FDE472509C0417B91438DCF0E6F2BF479BA340A3`.
  No unsound range assumption remains.

### Checks executed (scope stated)
- Static source extraction and inspection of B01–B11 plus G03–G12: candidate
  range lemma is FALSE; this is a source-level mathematical disproof of the
  proposed shortcut, not a Lean build.
- `git diff --check`: clean. Static hard-rule scan of B13: clean.
- `tools/project_status.py --check`: PASS (manifest declarations only).
- `ops/ci/LATEST.md` remains “no run yet”; all three lane targets are still
  **CI pending**.

### Still unproved / risks
- The eight B11-vs-S checks remain 310-by-at-most-168 literal kernel decisions.
  They are the first likely CI cost/failure point, but there is no CI evidence yet.
- `EnergyTerminalBatchB13Main` remains blocked on Lane A's missing C450 modules.
- `RemainingTerminalRadius` (389 ids) and `SevenClassExclusions` stay unpaid.

### Very next concrete step
Wait for real CI output. If a B11-vs-S check fails, do not use a global range:
split B11 hierarchically into its actual union components (B10 paid set plus the
210 G03–G12 `newIDs`, then further down only if needed) and prove pairwise
disjointness against S01..S08. Address only the first reported failing target.

## 2026-10-28 — explicit B13 residual census set (CI pending)

### Done
- Corrected an internal inconsistency: earlier notes said B13 “defines the
  389-id residual”, but the module only had the proposition
  `RemainingTerminalRadius`. Added `residualIDs`, the actual terminal ids not
  already paid by B13:
  `((univ.filter terminal=true).filter (n ∉ sharpIDs ∧ n ∉ paidIDs))`.
- Added `mem_residualIDs_iff` and `remaining_iff`, proving that
  `RemainingTerminalRadius` is exactly the pointwise radius premise over this
  set (with the same chart, feasibility and non-strict inequality arguments).
  This removes ambiguity about which terminal ids remain unpaid; it does not
  prove any radius estimate.
- `EnergyTerminalBatchB13.lean` is now 11414 UTF-8 bytes, sha256
  `54508878d90582a32b7fef23532fe8892d29d9c30ce002951181979e3f53a75b`.
  `TARGETS.txt`, `Paid16GeneralNext1182.lean` and B13Main are unchanged.

### Checks executed (scope stated)
- Static source inspection of `rest1182-emission-manifest.json`: its `spec`
  records `total_terminals: 2386` and `base_paid: 815`, while `n_records` is
  1182. Hence the prose count 2386−815−1182 = 389. Scope: manifest arithmetic,
  not a Lean proof and not a census over `DBMSourceTree.data`.
- `sha256sum` and `git diff --check`: clean. Hard-rule static scan of B13
  (forbidden proof escapes) found no matches; `project_status --check` PASSed
  (manifest declarations only).
- No local Lean build; all lane targets remain **CI pending**. `remaining_iff`
  and `mem_residualIDs_iff` are unelaborated.

### Still unproved / risks
- `residualIDs.card = 389` is NOT proved. The number comes from the manifest;
  proving it requires a kernel-checkable total-terminal count/census and the
  paid/sharp disjointness census. Do not quote 389 as a Lean theorem.
- `RemainingTerminalRadius` over `residualIDs` and `SevenClassExclusions` remain
  explicit unpaid premises. B13Main remains blocked on Lane A's C450 imports.
- The eight B11-vs-S01..S08 `decide +kernel` checks are still the heaviest
  energy-aggregate probes. If CI selects one as failure, split B11 as B10 plus
  G03..G12 by `Finset.disjoint_union_left` and use separate bounded checks.

### Very next concrete step
On the next session, read CI first. If B13 is green, prove the residual census
cardinality from a terminal-total theorem plus paid/sharp counts; if no such
theorem exists, add a bounded hierarchical census module rather than claiming
389. If B13 is red, fix only the first reported elaboration/kernel failure.
