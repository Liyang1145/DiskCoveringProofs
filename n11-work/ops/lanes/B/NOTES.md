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
