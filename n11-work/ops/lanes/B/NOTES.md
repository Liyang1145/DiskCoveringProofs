# Lane B notes

SUPERVISOR (2026-10-29 00:45 CST): Once CI reports on Next1182/B13, fix the first error only, re-run. Make `residualIDs.card = 389` a kernel fact (literal list, hierarchical <=170-literal decides) instead of manifest-derived. Then help lane C: write the generic emitter that turns an exact m-row certificate JSON into `PaidCellCertificateM` packets (21 per module).

## 2026-10-28 - session part 5: CI/literal-premise dependency audit (CI pending)

### Done
- Audited the literal-premise edge: `EnergyTerminalResidualCensus.RemainingTerminalRadius`
  is over exactly the 389-id literal census, `remaining_iff_b13` has the claimed
  direction, and `main_of_energy_literal_and_seven_classes` consumes it via
  `remaining_iff_b13.mp` before the B13-to-C450 conclusion. No type-direction bug
  was found in that edge. `residualIDs_card = 389` is already derived from four
  literal disjoint chunks (100/100/100/89), not a manifest count.
- GitHub API shows Lean run `40731771155` (`head_sha` `233818af`) **pending with
  no job**, so there is no first elaboration error to fix yet.

### Files and exact hashes (sha256)
- `n11-work/lean/N11Formalization/EnergyTerminalBatchB13Main.lean`
  `2A6A206FE49CD299FCA69221B12B888B55EF6A3A92E34189B3E48C72761D0F98`
- `n11-work/lean/N11Formalization/EnergyTerminalResidualCensus.lean`
  `FD771E472F50C1D6DC72D1336D064A3F0D5D8DC8D5790FE01C6933DE07451B56`
- `n11-work/ops/lanes/B/emit_residual_census.py`
  `6DBC9E7FEE38703335A22AC2462F965AF5ED58EE1C81A35678DD05F7F043197B`

### Checks executed (scope)
- Source inspection of the two `RemainingTerminalRadius` definitions and their
  iff lemma: PASS (dependency direction only; not Lean elaboration).
- `python tools/project_status.py --check`: PASS (manifest declarations only).
- No Lean build was run; all four B targets remain **CI pending**, not paid.

### Still unproved / next concrete step
- All 51 census block lemmas, B13 disjointness, both energy premises, and
  `SevenClassExclusions` remain unelaborated/unpaid. Next: when
  `40731771155` completes, read the first B-target failure, fix only that error,
  and append its exact log line and rerun state here.

## 2026-10-28 - session part 3: removed census kernel blowup (CI pending)

### Done
- Found that `residualIDs_sound` previously ran four `decide +kernel` checks over
  the 1,997-element `B13.paidIDs`. Replaced them with one proof derived after
  `residualIDs_eq` via `EnergyTerminalBatchB13.mem_residualIDs_iff`; no chunk now
  normalizes the paid set during soundness checking.
- Emitter regeneration still reconstructs 2,506 terminals, 120 sharp, 1,997
  paid, 389 residual and chunk sizes 100/100/100/89.

### Files and exact sha256
- `n11-work/lean/N11Formalization/EnergyTerminalResidualCensus.lean`
  `A0CE97CA2F774A1406A0C4B8CFEC55DCDC4250DAFDE60B7BF5D1A8C31202E15F`
- `n11-work/ops/lanes/B/emit_residual_census.py`
  `FC9E897D71D427585D2AFD48F12C49F6CDEC47F691365AB3138BD8288B27A3C3`
- `n11-work/ops/lanes/B/emit_residual_census-report.json`
  `0708675EA932A2EA0425136B96A176D5BBBDC3880C40A7D729D8D6DDE83F28A6`

### Checks executed (scope)
- `python3 emit_residual_census.py`: PASS, source reconstruction and emitted bytes.
- `python3 -m py_compile emit_residual_census.py`: PASS.
- Hard-rule scan of the generated module: PASS; `git diff --check`: PASS.
- `python tools/project_status.py --check`: PASS (manifest declarations only).
- GitHub Actions API: n11 run `40731771155` remains pending with no job; no Lean
  elaboration or current CI failure is available locally. **CI pending.**

### Still unproved
- `residualIDs_eq`, `remaining_iff_b13`, the 51 block checks, B13 disjointness,
  and the energy/SevenClassExclusions premises remain unelaborated/unpaid.

### Very next concrete step
Read the first CI failure for run `40731771155`. If `residualIDs_sound` or the
block checks are implicated, reduce the block checks next; otherwise fix only
that first failing target and append its exact error here.

## 2026-10-28 - session part 2: literal 389-ID premise (condensed, CI pending)

- Added `EnergyTerminalResidualCensus.RemainingTerminalRadius` over four literal
  chunks and `remaining_iff_b13`; added literal-energy wrappers in B13Main.
- Emitter/regeneration checks passed at source/byte level: 2,506 terminals,
  120 sharp, 1,997 paid, 389 residual, chunk sizes 100/100/100/89. No local
  Lean elaboration; all Lean claims remained CI pending. The exact 389 energy
  premise and `SevenClassExclusions` are still unpaid.
- Superseded hashes are preserved in git history; current hashes are in the
  session-part-4 entry. Next step is to read the first current CI failure.

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

### Earlier engineering history
- `Finset.disjoint_left.mp` requires `(a := a)`; fixed in Next1182 and B13.
- B11 straddles the 2565 boundary; if CI rejects it, split B11 into B10 plus
  G03-G12 rather than assuming a range.
- The old 389 claim was manifest arithmetic only; the literal reconstruction is
  now 2,506 terminals - 120 sharp - 1,997 paid = 389 residual.

## 2026-10-28 - session part 4: semantic B13 residual cardinal (CI pending)

### Done
- Added `b13_residualIDs_card : EnergyTerminalBatchB13.residualIDs.card = 389`
  to the deterministic census emitter/generated module. It rewrites the B13
  semantic set through `residualIDs_eq` and `residualIDs_card`; no new kernel
  decide is introduced. Emitter regenerated 2,506 terminals, 120 sharp,
  1,997 paid and 389 residual.
- API audit: n11 run `40731771155` remains pending with no job; runs
  `40731863840`/`40731863933` are the replay/delivery workflows, not Lean.

### Files (sha256)
- Lean `EnergyTerminalResidualCensus.lean`
  `FD771E472F50C1D6DC72D1336D064A3F0D5D8DC8D5790FE01C6933DE07451B56`
- `emit_residual_census.py`
  `6DBC9E7FEE38703335A22AC2462F965AF5ED58EE1C81A35678DD05F7F043197B`
- `emit_residual_census-report.json`
  `F0B342655F9CE2EA56F49BDD20570A07F401CDFC7533054DFA57C06494566518`

### Checks executed (scope)
- Emitter and `py_compile`: PASS at source/byte level; count assertions PASS.
- Forbidden-token scan of generated Lean: PASS; `git diff --check`: PASS.
- Project status: PASS (manifest/index declarations only).
- No local project Lean elaboration; new theorem is **CI pending**.

### Still unproved / next concrete step
- Unpaid: all 51 `mem_iff_block*` lemmas, `residualIDs_eq`, the new derived
  cardinal lemma, B13 disjointness and both mathematical premises.
- Next: read the first `n11-lean-build` failure for run `40731771155`; fix only
  that error, then rerun. Do not edit lane C files while doing so.
