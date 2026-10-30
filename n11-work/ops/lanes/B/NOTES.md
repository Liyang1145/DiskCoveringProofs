# Lane B notes

## Condensed history through 2026-10-30 part 4

- Next1182's eight-part `Finset.univ.biUnion` aggregate is CI green at source
  `5D941203...`: 1182 ids, 57 literal blocks (max 21), 28 disjointness facts,
  and eight `omega` lower-bound transfers.
- Next505Bounds `FA5CA6EB...` and B13Next505Bounds are CI green.
- Run `40973981403` (`76b6835e`) exited 0 for Next1182 and Next505Bounds, then
  failed the older B13 source at two uses of the nonexistent
  `Finset.all_eq_true.mp`. That revision was replaced; current B13 and B13Main
  remain **CI pending / unpaid**.
- Earlier run failures included shared frozen-dependency OOM kills and a root
  OOM in `SharedMomentConcreteSwitchBatch`; neither is a lane-B mathematical
  verdict. A source/inventory/byte audit is never Lean proof credit.

## Retained engineering facts

### Next1182
- Cardinality is `Finset.card_biUnion hdisj`; membership uses `mem_biUnion` and
  `fin_cases`. Pairwise disjointness unfolds through `Function.onFun`, hence
  `change Disjoint (part i) (part j)` before dispatch.
- Part-local lower bounds transfer to global 2565 using the full conjunctive
  bound plus `omega`; never project only the part-local left endpoint.
- The old trailing `norm_num` in `new_count` caused `No goals to be solved`.

### B13 / Next505
- B13Next505Bounds replaces the 505-id decode with 25 blocks (24x21 plus one).
- B13 now imports `EnergyTerminalBatchB13DescentBounds`: B10 is split into B09
  (58-id decode) and First42 (42-id decode); Remaining210 is ten 21-id G03..G12
  blocks. The largest new kernel decode is 58 literals.
- B13Main forwards residual 389 through B12's `remaining_of_b12`; the
  literal-census variant uses `EnergyTerminalResidualCensus.remaining_iff_b13`.
- **ROOT-IMPORT REQUEST (only after CI green):** import
  `EnergyTerminalBatchB13Main` instead of `EnergyTerminalBatchB12Main`.

### Working rules retained
- `Finset.card_biUnion` takes disjointness explicitly;
  `Finset.disjoint_left.mp` needs `(a := a)` when the element is implicit.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`, `emit_b13_descent_bounds.py`. Audits:
  `audit_next1182_blocks.py`, `audit_b13_descent.py`, `audit_b13main.py`.
- Do not claim payment for Next1182, B13, or B13Main without a matching CI exit 0.

## 2026-10-30 - session part 5: bounded B13 descent

### Done
- Re-read GUIDANCE/Lane B/NOTES/CI and ran `project_status.py --check` (exit 0).
- Added `EnergyTerminalBatchB13DescentBounds.lean`. It proves `b10_lt` by
  splitting B10 into B09 plus First42, and proves `remaining210_lt` by ten
  per-group `G03..G12` decodes plus `Finset.mem_union` dispatch. This removes
  the 210-id direct decode formerly embedded in B13.
- Rewired B13's `b11_lt` to the two bounded theorems and added the new module
  before B13 in `TARGETS.txt`.
- Emitter `emit_b13_descent_bounds.py`: `py_compile` exit 0; rerunning it
  reproduced the module byte-for-byte. `audit_b13_descent.py` exit 0: ten group
  blocks, 12 kernel decisions, max claimed decode 58, no direct 210-id decode,
  B13 import/reference present, no forbidden tokens.
- Re-ran existing lane audits (exit 0): Next1182 1182 ids/57 blocks/top SHA
  `5D941203...`; B13 inventory 310+505+1182=1997 paid, 2506 terminals, 120 sharp,
  residual 389, all 13 checks pass; B13Main static import/API audit passes.
- `git diff --check` exit 0. `audit_target_imports.py` first hit a 60 s bound,
  then completed under a 180 s bound (exit 0): 1920 modules in the local import
  closure, no missing imports, no forbidden tokens. This is static closure only.

### Files (SHA256, uppercase)
- `EnergyTerminalBatchB13DescentBounds.lean` `519EEF7E0A435C65A86C1DC8401ADAF534278E3862A9B83031947B3333DD0E85`.
- `EnergyTerminalBatchB13.lean` `E850E7B0BFF305411374F49E1FFC371494BEF5F70749E6F9B864DD3B1191EB38`.
- `emit_b13_descent_bounds.py` `6AFD8C80AA5C66367007F04A4A028571635528DBB839E9D598B8E8379F88F8CD`.
- `audit_b13_descent.py` `D5C4920CA6D3E4E98B7A234D6EB05A45871F64BE8311042880776345B65EEAC1`.
- `TARGETS.txt` `4E8E73251E43B27E7297C5D6CB21BD04FB93195021A5128C364A09795A476600`.

### Still unproved / unverified
- The new descent module, repaired B13, and B13Main are **CI pending / unpaid**;
  only source/inventory audits ran locally. Residual 389,
  `SevenClassExclusions`, and the arbitrary-center full-disk theorem remain
  mathematically unpaid.

### Next concrete step
- On the first CI run binding these hashes, require exit 0 first for
  `EnergyTerminalBatchB13DescentBounds`, then B13, then B13Main. If red, quote
  the first module-local error; if green, issue the root-import request.

## 2026-10-30 - session part 6: post-repair triage

### Done
- Reloaded GUIDANCE/Lane B/NOTES/LATEST and ran bounded
  `project_status.py --check` (exit 0; manifest declarations only).
- Confirmed the current source hashes still bind the repaired B13:
  B13 `E850E7B0...`, B13Main `2A6A206F...`, DescentBounds `519EEF7E...`,
  TARGETS `4E8E7325...`. `LATEST.md` is still run `40973981403` and predates
  this repair, so there is no post-repair CI verdict yet.
- Rechecked the visible new disjointness proof: B12 splits into B11 and
  Next505; both sides are bounded below 2565 while all Next1182 ids are >=2565.
  No source defect found in that argument by static inspection.
- Ran `audit_b13_descent.py` (exit 0): 10 group blocks, 12 kernel decisions,
  max 58-literal decode, bounded B10/B210 paths, no forbidden tokens.
- Ran `audit_b13main.py` (exit 0): imports/API/inventory complete; static only.
- `git diff --check` exit 0.
- Attempted a Mathlib-probe check of `Finset.disjoint_union_left` and
  `card_union_of_disjoint` patterns. The probe has no cached Mathlib oleans;
  imports exceeded the 120 s bound and were killed. This is a tooling failure,
  not Lean evidence.

### Files
- No source changes this session; B13 hash remains `E850E7B0...`.
- `NOTES.md` updated only.

### Still unproved / unverified
- DescentBounds, repaired B13, and B13Main remain CI pending / unpaid.
- Residual 389, SevenClassExclusions, and the arbitrary-center full-disk
  theorem remain unpaid.

### Next concrete step
- On the first CI run binding `E850E7B0...` (B13), require exit 0 for
  DescentBounds, B13, then B13Main. If red, use the first module-local line;
  if green, issue `ROOT-IMPORT REQUEST: import EnergyTerminalBatchB13Main
  instead of EnergyTerminalBatchB12Main`.
