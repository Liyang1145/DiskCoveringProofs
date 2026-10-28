# Lane B notes

SUPERVISOR (2026-10-29 00:45 CST): Once CI reports on Next1182/B13, fix the first error only, re-run. Make `residualIDs.card = 389` a kernel fact (literal list, hierarchical <=170-literal decides) instead of manifest-derived. Then help lane C: write the generic emitter that turns an exact m-row certificate JSON into `PaidCellCertificateM` packets (21 per module).

## 2026-10-28 - B13Main credit-transfer type fixed (CI pending)

### Done
- Confirmed `residualIDs_card = 389` is already a literal hierarchical kernel
  fact (four disjoint literal chunks of 100/100/100/89; all `decide +kernel`
  checks see at most 101 literals), not a manifest-derived count. Re-ran the
  deterministic emitter and reproduced the exact module hash.
- Lane A's `C450ChainCompletionMain.lean` is now present. Its consumer requires
  `EnergyTerminalBatchB11.RemainingTerminalRadius`, but B13Main passed the B12
  premise directly. Fixed the edge in `EnergyTerminalBatchB13Main.lean` by
  composing `EnergyTerminalBatchB12.remaining_of_b12` with
  `EnergyTerminalBatchB13.remaining_of_b13`.

### Files and exact hashes (sha256)
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Main.lean`
  `A9F0FB735497EB7875FFB320BDBEF37ED4423FBA7975939FDD0C58EC191E4491`
- `n11-work/lean/N11Formalization/C450ChainCompletionMain.lean` (Lane A input)
  `942DD90F69781A7CE1D57C5A393C3C11626CFE4135B30C5834FB2656CA3B6C03`
- `n11-work/lean/N11Formalization/EnergyTerminalResidualCensus.lean`
  `B9504B9282D87E3D3FA85842E538A5CCB6CABE5234F1A8AC27F08C3AFBF0C362`

### Checks executed (scope stated)
- `python3 n11-work/ops/lanes/B/emit_residual_census.py`: PASS; reproduced
  2,506 terminals, 120 sharp, 1,997 B13 paid, 389 residual and the exact Lean
  hash above.
- Static hard-rule scan of B13Main: PASS. `git diff --check`: PASS.
  `python tools/project_status.py --check`: PASS (manifest/index declarations
  only). No Lean elaboration was run locally; all targets remain CI pending.

### Still unproved / risks
- The B13Main type composition is source-checked but not elaborated; CI must
  confirm it. The 16 B13 disjointness checks and 51 census interval blocks also
  remain CI pending.
- `RemainingTerminalRadius` and `SevenClassExclusions` remain explicit unpaid
  premises. B13Main is conditional and is not the full-disk theorem.

### Very next concrete step
When CI reports, fix only the first B-lane target error and rerun. If all four
B targets are green, request the root import switch to
`EnergyTerminalBatchB13Main`; otherwise do not request it.

## 2026-10-28 — residual equality made blockwise (CI pending)

### Done
- Replaced the two whole-table `decide +kernel` checks in
  `EnergyTerminalResidualCensus.lean` with emitted small checks:
  four 100/100/100/89 chunk soundness lemmas, and 51 source-index interval
  lemmas (`mem_iff_block00` ... `mem_iff_block50`), each covering at most 100
  `Fin 5011` values. Each block rewrites semantic membership through
  `EnergyTerminalBatchB13.mem_residualIDs_iff` before deciding, avoiding a
  repeated scan of `Finset.univ.filter`; `residualIDs_eq` dispatches an `omega`
  interval cover.
- Kept `residualIDs_card = 389` hierarchical; no global semantic-filter decide
  or manifest count remains in this module.
- Regenerated the module and report from the checked-in source reconstruction.

### Files and exact hashes (sha256)
- `n11-work/lean/N11Formalization/EnergyTerminalResidualCensus.lean`
  `B9504B9282D87E3D3FA85842E538A5CCB6CABE5234F1A8AC27F08C3AFBF0C362`
- `n11-work/ops/lanes/B/emit_residual_census.py`
  `fad4a8fe49d46008d6aa3616b378ee140c6a5f4f59388fb11ffffe7a9ec5092d`
- `n11-work/ops/lanes/B/emit_residual_census-report.json`
  `76a56f3c032d7a4eb46c10b72e354eac763ce65dd1bbd878792523e817ca5fe8`
- `n11-work/ops/lanes/B/TARGETS.txt` unchanged
  `8f8ba4842f17f3be779a979eb3a69d17b1313d3d2967a017a4dd359d9b74b179`

### Checks executed (scope stated)
- `python3 n11-work/ops/lanes/B/emit_residual_census.py`: PASS; reconfirms
  terminals 2506, sharp 120, B13 paid 1997, residual 389 and all set relations.
- `python3 -m py_compile .../emit_residual_census.py`: PASS.
- Generated Lean hard-rule scan: no `sorry`, `admit`, `axiom`,
  `native_decide`, `ofReduceBool`, `implemented_by`, or `maxHeartbeats 0`.
- `git diff --check`: PASS. `python tools/project_status.py --check`: PASS
  (manifest declarations only).
- A Mathlib-probe micro-test of the interval/`omega` proof shape timed out at
  120 s during import, so it produced no Lean result. No project Lean build was
  run locally; every Lean target remains **CI pending**, not paid.

### Still unproved / risks
- Elaboration of the 51 new interval lemmas is CI-pending. If one fails, check
  that block's interval endpoints and use the reported node rather than
  widening kernel scope.
- B13's 16 disjointness checks and the explicit `RemainingTerminalRadius` and
  `SevenClassExclusions` premises remain unpaid. `B13Main` remains blocked on
  Lane A's missing C450 completion module.

### Very next concrete step
Read CI. If red, fix only the first B-target error and rerun; if green, request
the root import switch to `EnergyTerminalBatchB13Main`, then implement Lane C's
generic exact m-row `PaidCellCertificateM` packet emitter (21 packets/module).

## 2026-10-28 - literal 389 residual census emitted (CI pending)

### Done
- Independently reconstructed the terminal census from the checked-in Lean
  sources, not from `total_terminals`: all 5,011 `DBMSourceTreeData.nodeN`
  declarations give 2,506 `terminal = true` nodes; `patchID` gives 120 sharp
  ids; B11 = 310, Next505 = 505, Next1182 = 1,182, hence B13 paid = 1,997.
  These sets are disjoint as required and leave exactly 389 residual ids.
- Added deterministic emitter `n11-work/ops/lanes/B/emit_residual_census.py`.
  It reconstructs the 12 G-packet arrays, four B03-B09 packet arrays, the 25
  literal Next505 groups, the Next1182 manifest, the terminal table and the
  sharp array; it asserts counts 2,506 / 120 / 1,997 / 389 and all set
  relations before writing Lean.
- Generated `N11Formalization/EnergyTerminalResidualCensus.lean` with four
  sorted literal chunks of sizes 100/100/100/89. The card proof uses three
  `decide +kernel` disjointness checks and four chunk-card checks, all <=101
  literals. It also drafts `residualIDs_sound` (all literal ids are terminal,
  non-sharp and unpaid) and `residualIDs_eq` (literal set equals B13's semantic
  filter).
- Registered `N11Formalization.EnergyTerminalResidualCensus` in `TARGETS.txt`.

### Files and hashes (sha256; bytes where noted)
- `n11-work/lean/N11Formalization/EnergyTerminalResidualCensus.lean`
  `96326301750AACB7B4AE9C5F6D0EA56D3D8EC9EB5146535789E44F4DAD2991E1`
  (generated bytes; report records the same hash in lowercase).
- `n11-work/ops/lanes/B/emit_residual_census.py`
  `b4cbbfb13dfe1493f8df4d50a5e013fd6c5ccec68d19808eb6004d9197dc62bc`.
- `n11-work/ops/lanes/B/TARGETS.txt`
  `8f8ba4842f17f3be779a979eb3a69d17b1313d3d2967a017a4dd359d9b74b179`.
- `n11-work/ops/lanes/B/emit_residual_census-report.json`
  `74476982e615ac611fe777bdb3ad82b7530f3bb868f46a6860c155405a3f3916`;
  source manifest hash is recorded inside.

### Checks executed (scope stated)
- `python3 n11-work/ops/lanes/B/emit_residual_census.py`: PASS; source-level
  reconstruction asserts all counts/relations above and rewrites the module.
- `python3 -m py_compile .../emit_residual_census.py`: PASS.
- Static hard-rule scan of the generated Lean: no `sorry`, `admit`, `axiom`,
  `native_decide`, `ofReduceBool`, `implemented_by`, or `maxHeartbeats 0`.
- `python tools/project_status.py --check`: PASS; manifest declarations only,
  not mathematics or complete byte integrity.
- `git diff --check`: PASS. `ops/ci/LATEST.md` still says "no run yet".
- No Lean build was run locally (full project oleans absent; 2-core worker).
  All Lean targets remain **CI pending**, not paid.

### Still unproved / risks
- `EnergyTerminalResidualCensus.residualIDs_card` is drafted but unelaborated.
  `residualIDs_eq` is the likely CI cost point because it decides equality with
  the 5,011-element semantic filter; if red, replace it with a structural
  terminal/paid/sharp partition proof rather than increasing limits blindly.
- `EnergyTerminalBatchB13.RemainingTerminalRadius` (now exactly 389 ids) and
  `ActualMetricClassReduction.SevenClassExclusions` remain explicit unpaid
  premises. `C450ChainCompletionMain` is still absent in this worktree, so
  `EnergyTerminalBatchB13Main` remains blocked on Lane A.
- The 16 B13 disjointness checks (B11/Next505 against eight Next1182
  sub-aggregates) were already unelaborated before this module; they remain the
  other likely CI cost point.
- The live delivery manifest was not edited because this lane is restricted to
  lane files and new Lean modules. The supervisor should add the four new or
  maintained files above to `manifests/FILES.jsonl` / `SUMMARY.json` without
  changing original proof entries.

### Very next concrete step
Read CI. If green, request the root import switch to
`EnergyTerminalBatchB13Main` and preserve B12Main. If red, fix only the first
reported target/error, then rerun. After B13 is green, implement Lane C's
generic exact m-row certificate emitter into `PaidCellCertificateM` packets (21
per module), keeping the existing exact-rational self-check.

## Condensed prior history (all still CI pending)

### Stage-2 aggregate and B13 draft
- Root blocker was an upstream Windows-path bug in `emit_aggregate_hier.py`;
  lane-local `emit_next1182_top.py` reproduced the frozen top module bytes
  before applying the implicit-binder fix.
- `Paid16GeneralNext1182.lean` sha256 (corrected):
  `5F6CB04F84D20AE127DE13498E6929BCE3E3C5BABFA751EF99BE630D0266CB17`.
- `EnergyTerminalBatchB13.lean` sha256:
  `54508878D90582A32B7FEF23532FE8892D29D9C30CE002951181979E3F53A75B`.
  It proves `paid_count = 1997`, `paid_not_sharp`, terminal/radius dispatch,
  exact `remaining_iff` over the semantic residual filter, and
  `remaining_of_b13 : B13.RemainingTerminalRadius -> B12.RemainingTerminalRadius`.
- `EnergyTerminalBatchB13Main.lean` sha256:
  `7685A0FFE7C192BC997EBD6FB5D17B96C197ABC72C42E43B319D9CA47655683C`.
  It conditionally transfers B13 to the C450 main theorem and the full-disk
  corollary. **ROOT-IMPORT REQUEST (after CI green):** import B13Main instead
  of B12Main.

### Disjointness engineering
- The `⦃a⦄` implicit binder in `Finset.disjoint_left.mp` requires `(a := a)`;
  positional calls were fixed in Next1182 (8) and B13 (16).
- B11 straddles the 2565 boundary (2162/2166 and 3436, 4179/4265, 4267), so a
  global `n.val < 2565` shortcut is false and was reverted. Disjointness is
  split into eight B11-vs-S and eight Next505-vs-S checks; if CI rejects one,
  split B11 further into B10 plus G03-G12 rather than using a range assumption.

### Residual-set history
- Earlier B13 exposed only the proposition; it then gained a semantic
  `residualIDs` filter plus `mem_residualIDs_iff` and `remaining_iff`.
- The previous 389 claim came only from manifest arithmetic
  (`2386 - 815 - 1182`), which incorrectly suggested total terminals were 2,386
  before subtracting sharp. The current source-level reconstruction resolves
  this: 2,506 total terminals, 120 sharp, 1,997 paid, 389 residual.
