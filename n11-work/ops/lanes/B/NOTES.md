# Lane B notes

## 2026-10-29 - session part 14: diagnose stale CI lower-bound failures

### Done
- Re-read GUIDANCE, LANES, part-13 notes and CI LATEST. Mapped CI run
  `40914236268` error lines to committed `0AFA07FB...`, not current worktree
  `F63677C5...`.
- Root cause of the seven `Type mismatch` errors: in `0AFA...`, part 1 uses
  `exact (part_s01_bounds n h).1` because its lower endpoint is 2565, but
  parts 2-8 start at 2737, 2907, 3088, 3267, 3446, 3955 and 4986. The current
  emitter transfers each part-local bound with `have hb` + `omega`, which
  covers the global target 2565; its 64-case disjointness dispatch is already
  explicit.
- Added regression assertions to `audit_next1182_blocks.py`: exactly eight
  global lower-bound transfers and zero direct `exact (part_s...)` proofs.

### Checks executed (scope)
- `audit_next1182_blocks.py`: exit 0 on `F63677C5...`; 8 parts, 57 literal
  blocks (max 21 cases), 28 interval-disjoint theorems, 8 diagonal + 56
  off-diagonal dispatch branches, 8 transfers, 0 direct part exacts, 0 kernel
  decodes. Scope is source/manifest inventory, **not Lean elaboration**.
- `python tools/project_status.py --check`: passed (handoff index only).
- `git diff --check` and forbidden-token scan: clean.
- A minimal Mathlib `omega` probe exceeded its 100s local cap and produced no
  verdict; no Lean elaboration claim.

### Still unproved / unverified
- `Next1182` `F63677C5...`, Next505Bounds, B13 and B13Main remain **CI
  pending / unpaid**. B13Main root import still requires CI green. Residual
  389, `SevenClassExclusions`, and the arbitrary-center full-disk theorem
  remain unpaid.

### Next concrete step
- On the next CI run, inspect `F63677C5...` first and quote the first genuine
  Next1182 error if any. If green, require separate exits for Next505Bounds,
  B13 and B13Main before requesting the root import.

## 2026-10-29 - session part 13: audit the repaired 64-case dispatch

### Done
- Re-read GUIDANCE, LANES, part-12 notes and CI LATEST. Latest shown run
  `40914236268` still reports the pre-fix Next1182 bytes; current worktree
  bytes are the repaired SHA256 `F63677C532B2778AAB72D3AFD8C0EFF9B6AA00C3E7328A3EDD4601016186DAB3`.
- Strengthened `audit_next1182_blocks.py` to check the exact `hdisj` dispatch
  inventory: 8 `fin_cases j`, 8 diagonal `(hij rfl).elim` branches, 56
  off-diagonal `simpa [part] using disjoint_s...` branches, and 28 `.symm`
  uses. This closes the static risk that one of the 64 ordered pairs was
  omitted or duplicated.
- Rechecked B13Main's direct API chain: `remaining_of_b13` -> B12
  `remaining_of_b12` -> `C450ChainCompletionMain`; the literal-census variant
  uses `EnergyTerminalResidualCensus.remaining_iff_b13` in the expected
  direction. `audit_b13main.py` remains clean.

### Checks executed (scope)
- `python tools/project_status.py --check`: passed (handoff index only).
- `audit_next1182_blocks.py`: passed; manifest 1182 ids, part sizes
  `168x7+6`, 57 literal blocks of at most 21 cases, 28 interval-disjoint
  theorems, 8 diagonal + 56 off-diagonal dispatch branches. Scope is source,
  manifest and proof-shape inventory, **not Lean elaboration**.
- `audit_b13main.py`: passed static imports/API. SHA256:
  Next1182 `F63677C5...`; B13 `79CE135A...`; B13Main `2A6A206F...`.

### Still unproved / unverified
- Next1182, Next505Bounds, B13 and B13Main remain **CI pending / unpaid**.
  No local Lean build exists; this session made no elaboration claim.
- Residual 389, `SevenClassExclusions`, and the arbitrary-center full-disk
  theorem remain unpaid.

### Next concrete step
- On the next CI run, inspect Next1182 first and quote the first genuine error
  if any. If green, require explicit exits for Next505Bounds, B13 and B13Main;
  only then issue the root-import request.

## 2026-10-29 - session part 12: CI target for B13Main

### Done
- Re-read current bytes after CI `40914236268`: the reported Next1182 errors
  are on the pre-fix file, but the worktree now has SHA256
  `F63677C532B2778AAB72D3AFD8C0EFF9B6AA00C3E7328A3EDD4601016186DAB3`
  with `.1`/`omega` lower-bound branches and explicit 64-case `hdisj`.
- Added `N11Formalization.EnergyTerminalBatchB13Main` to TARGETS. The module
  was already present, statically audited, and forwards B13 residual 389 to
  B12 via `remaining_of_b13`; it was not previously kernel-checked by CI.
- Added a lane-local Mathlib probe for the exact pairwise-disjoint dispatch
  shape. `import Mathlib` exceeded the 120s timeout without a verdict; no Lean
  conclusion is claimed from it.

### Checks executed (scope)
- `python tools/project_status.py --check` passed (handoff index only).
- `audit_b13_closure.py` passed all 13 inventory checks: B13=1997,
  residual=389, terminals=2506, sharp=120; scope is inventory equality only.
- `audit_b13main.py` passed all static import/API checks.
- `audit_target_imports.py` passed over a 1919-module closure with no missing
  imports and no forbidden proof escapes; scope excludes Lean elaboration.
- SHA256 and source inspection of current Next1182/B13Main; TARGETS update.
- Local probe timed out at 120s (scope: tactic syntax only, no verdict).

### Still unproved / unverified
- `F63677C5...` is **CI pending / unpaid**; Next505Bounds, B13, and B13Main
  are also **CI pending**. Residual 389, `SevenClassExclusions`, and the
  arbitrary-center theorem remain unpaid.

### Next concrete step
- On the next CI run, quote the first genuine error for `F63677C5...`; if it
  passes, check B13 then B13Main. Only request the root import after B13Main
  is CI green.

## 2026-10-29 - session part 11: fixed Next1182 lower-bound and hdisj proofs

### Done
- Quoted CI run `40914236268` errors: `Paid16GeneralNext1182.lean:582-588`
  part-local lower bounds were passed directly to global `2565 ≤ n.val`, and
  line 590 had an unsolved `hdisj` goal. B13 showed no independent error line in
  `errors_head`; its exit 1 is consistent with the failed Next1182 dependency.
- Updated `emit_next1182_top.py`: each `lower_bound` branch now extracts the
  part-local lower bound then uses `omega`; `hdisj` now dispatches all 64 ordered
  `Fin 8` pairs explicitly, using `(hij rfl).elim` on the diagonal and the named
  interval-disjoint theorem (or its `.symm`) off diagonal.
- Regenerated `Paid16GeneralNext1182.lean` (40,899 bytes). Structure remains
  8 parts of `168x7 + 6`, 57 literal blocks with max 21 cases, 28 disjointness
  theorems, and zero kernel decodes.

### Files (SHA256, uppercase)
- Next1182 `F63677C532B2778AAB72D3AFD8C0EFF9B6AA00C3E7328A3EDD4601016186DAB3`.
- Emitter `893DA20241B45E63255EAD5F2E38947A3F2F07D8EE666B96B0A6890C79B2D2F4`.
- TARGETS unchanged. B13 bytes unchanged
  `79CE135A14299ACC32CB324FB8D8ABD69346B6E1303C5FAC68031C631A87B51F`.

### Checks executed (scope)
- Regeneration, `audit_next1182_blocks.py`, `py_compile`, `git diff --check`,
  and forbidden-token scan all exit 0. Scope is source/inventory only; **not
  Lean elaboration**. A Mathlib tactic probe exceeded its 120s cap and produced
  no verdict.

### Still unproved / unverified
- New `F63677C5...` is **CI pending / unpaid**. Next505Bounds, B13, B13Main,
  residual 389, `SevenClassExclusions`, and the arbitrary-center theorem remain
  unpaid.

### Next concrete step
- On CI for `F63677C5...`, quote the first genuine Next1182 error. If green,
  inspect B13's own elaboration independently, then B13Main. Do not request the
  root import until B13Main is CI green.

## 2026-10-29 - session part 10: replaced fragile part witnesses

### Done
- CI failures at `Paid16GeneralNext1182.lean:276+` were part-bound `Type
  mismatch`s in typed `le_trans` endpoint witnesses; literal block proofs were
  not implicated. Replaced all 57 part branches with
  `have hb := block_*_bounds n h_*` then `constructor <;> omega`, avoiding
  overloaded numeral/endpoint inference.
- Regenerated the module and reran the exact inventory audit (exit 0): 1182
  ids, parts `168x7 + 6`, 57 blocks, max 21 cases, 28 disjointness theorems,
  zero top-level kernel decodes.

### Files (SHA256, uppercase)
- Next1182 `0AFA07FB3BC7BB66C147CFC9B213993ABC2FE4646D8EE16FA6018F3802049D1B`
  (38,267 bytes); emitter
  `ED681C7D2FC4D3965133F4E9F00715598BFD7619AC59AE9BDA4356FE8C6DE6AD`.
- TARGETS unchanged (`Next1182`, `Next505Bounds`, `B13`); B13 unchanged
  `79CE135A14299ACC32CB324FB8D8ABD69346B6E1303C5FAC68031C631A87B51F`.

### Checks executed (scope)
- Emitter and audit exit 0; `py_compile`, `git diff --check`, forbidden-token
  scan clean. Scope is source/inventory only; **not Lean elaboration**.

### Still unproved / unverified
- New `0AFA07FB...`, Next505Bounds, and B13 are **CI pending / unpaid**.
  B13Main, residual 389, `SevenClassExclusions`, and arbitrary-center theorem
  remain unpaid.

### Next concrete step
- On CI for `0AFA07FB...`, quote the first genuine Next1182 error. If green,
  inspect Next505Bounds then B13 independently. Do not expand TARGETS early.

## Prior B13/Next1182 engineering (condensed)

### Next1182
- Top aggregate is `Finset.univ.biUnion part` over eight sub-aggregates.
  Membership is dispatched with `mem_biUnion` plus `fin_cases`; cardinality
  uses `Finset.card_biUnion hdisj` and `Fin.sum_univ_succ`.
- The prior `new_count` trailing `norm_num` caused `No goals to be solved` and
  was removed. A local Mathlib probe confirmed the 8-part/28-disjointness
  `hdisj` pattern.
- Source was split after a CI timeout: 57 literal blocks of at most 21 ids,
  with 21-literal kernels only. Stale CI `40901508838` tested older bytes.

### B13 / Next505
- Added `EnergyTerminalBatchB13Next505Bounds`, replacing B13's single
  505-element kernel decode with 25 literal blocks (24x21 plus one id). B13's
  private `next505_lt` delegates there.
- Next505 module SHA256
  `FA5CA6EB9CD75158085EDDD3C0CB464AB7F96CF124FCE40C303EB176D31D46F2`;
  emitter `emit_next505_bounds.py` SHA256
  `BFE4A4C422CDF5F54E60AD21E9C78AE96BDBBC7FD7717556B3FACFAE9203480A`.
- B13 descent: `b11_lt` uses B10 (100 ids) plus Remaining210 (210 ids);
  `next505_lt` uses the 25-block module. Thus B13 has no whole-505/1182
  decode. B10/210 remain explicit per-decode risk.
- If B13 fails in `b10_lt` or `remaining210_lt`, split those decodes into
  hierarchical literal bounds rather than increasing timeout.

## Retained engineering facts
- **ROOT-IMPORT REQUEST (only after CI green):** import
  `EnergyTerminalBatchB13Main` instead of `EnergyTerminalBatchB12Main`.
- `Finset.card_biUnion` takes disjointness explicitly:
  `Finset.card_biUnion hdisj`; `Fin.sum_univ_succ` expands the sum.
- `Finset.disjoint_left.mp` needs `(a := a)` in generated proofs.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`; audit: `audit_next1182_blocks.py`.
- A successful source/inventory audit is not proof. CI remains the only Lean
  build authority for project modules; Mathlib probes need `/workspace/tools/mathlib-probe`.
- Do not claim payment for Next1182, Next505Bounds, or B13 until CI is green.
