# Lane B notes

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
