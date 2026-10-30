EXPERT (2026-10-30):
- Next1182 and Next505 are green; B13 is not. Do not claim energy 1997 until DescentBounds, B13, and B13Main each exit 0.
- Highest leverage: remove `maxRecDepth 10000` by fixing `g03_lt`…`g12_lt`. `decide +kernel` traverses `univ.image nodeID` over Fin 5011, not 21 literals.
- Replace each with `obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn; fin_cases i <;> norm_num [Paid16GeneralGxx.nodeID]`.
- Apply the same image/union split to `first42_lt` and `b09_bound`; keep the corrected 27-id high classification.
- Build only DescentBounds, then B13, then B13Main; read the first module-local error if red.
- If all three are green, request the supervisor replace the root B12Main import with B13Main. Only then does credit move 815→1997 and residual move to 389.

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

## 2026-10-30 - session part 7: B09 counterexample and disjointness repair

### Done
- Fetched public artifact for run `40988698121` (sha `2fdf1a1c`; merge includes
  lane-B `a98495ec`). Lane-B exits: Next1182 0, Next505Bounds 0,
  DescentBounds 1, B13 1, B13Main 1. DescentBounds failed at all 12 former
  `decide +kernel` sites with kernel deep recursion.
- Static reconstruction exposed a real false theorem, not merely recursion:
  `B09.paidIDs` has 27 ids at or above 2565 (including 2661, 3436, 4179,
  4265, 4266, 4267, 4348, 4485). The prior `b09_lt : ... < 2565` and the
  B13 lower-bound-only disjointness argument were therefore invalid.
- Replaced it by exact `b09HighIDs` (27 literals), `b09_bound : n.val < 2565
  ∨ n ∈ b09HighIDs`, `b11_bound`, and `high_not_next`: every high id is
  excluded from all 57 literal Next1182 blocks via their public `mem_idsNN`
  disjunctions. B13 now consumes this classification in `new_disjoint_old`.
- Added finite `set_option maxRecDepth 10000` for the 58-id B09 exhaustive
  classification, matching the project's generated packet modules. No
  `maxHeartbeats 0`, `sorry`, axiom, or native decision was introduced.
- `audit_b13_descent.py` now checks the high-id classification/exclusion rather
  than the false `< 2565` claim: exit 0. `audit_b13main.py` exit 0;
  `audit_next1182_blocks.py` exit 0 (57 blocks, 28 interval pairs);
  `git diff --check` exit 0. All are static/source audits, not Lean credit.

### Files (SHA256, uppercase)
- `EnergyTerminalBatchB13DescentBounds.lean` `075B663ABF635B1F2E4584BFC6F18B7833181231B794F0125B033F10EEDED60B`.
- `EnergyTerminalBatchB13.lean` `3DD37313505E0E8D608D50D42D3AFB1F1E08CEBBDF1ACD5DB570F57D9DC8FD03`.
- `audit_b13_descent.py` `6E0ECC673A026BFB799F7F6CEEDC2ABB4C2D1B0FE9FCF5FEB68711E46EAE3C2D`.
- `TARGETS.txt` unchanged `4E8E73251E43B27E7297C5D6CB21BD04FB93195021A5128C364A09795A476600`.

### Still unproved / unverified
- The corrected DescentBounds and B13 are **CI pending / unpaid**; the
  409886 verdict is red for the superseded hashes. B13Main and the 389 residual
  remain unpaid, as do SevenClassExclusions and the full-disk theorem.
- `emit_b13_descent_bounds.py` still emits the superseded false `b09_lt`
  source and must not be rerun until ported to the high-id classification.

### Next concrete step
- On the next CI run binding `2E54EB03...`/`3DD37313...`, read the first
  DescentBounds error if red; if all three lane-B exits are 0, update the root
  import request from B12Main to B13Main. Immediately port the emitter's B09
  section to the checked-in high-id classification.

## 2026-10-30 - session part 8: emitter restored to corrected B09 proof

### Done
- Reloaded GUIDANCE/LANES/Lane-B NOTES/CI and ran `project_status.py --check`
  (exit 0; handoff manifest declarations only, not math).
- Replaced the stale `emit_b13_descent_bounds.py`, which still generated the
  known-false `b09_lt`, with a deterministic emitter for the corrected source.
  It now emits all 27 high ids, the 57 literal Next1182 blocks, and all 27 x 57
  exclusion branches. Regenerating reproduced the corrected Lean byte-for-byte.
- Extended `audit_b13_descent.py` to execute the emitter, require exact module
  byte reproduction, parse the 27 high ids and 57 literal block definitions,
  and require their 1182-id union to be disjoint from the high-id set.
- No Lean target list change: the corrected DescentBounds, B13, and B13Main were
  already present in `TARGETS.txt`.

### Files (SHA256, uppercase)
- `EnergyTerminalBatchB13DescentBounds.lean` `075B663ABF635B1F2E4584BFC6F18B7833181231B794F0125B033F10EEDED60B`.
- `EnergyTerminalBatchB13.lean` `3DD37313505E0E8D608D50D42D3AFB1F1E08CEBBDF1ACD5DB570F57D9DC8FD03`.
- `EnergyTerminalBatchB13Main.lean` `2A6A206FE49CD299FCA69221B12B888B55EF6A3A92E34189B3E48C72761D0F98`.
- `emit_b13_descent_bounds.py` `FBBC8E151204384899F2B8333B955957F3369CB0D142906A9EE4A55CB17B441D`.
- `audit_b13_descent.py` `7BDE34003EE17CF685B42E3DFF48C15885B981CDEA336D87E86D70633D6D32CF`.
- `TARGETS.txt` unchanged `4E8E73251E43B27E7297C5D6CB21BD04FB93195021A5128C364A09795A476600`.

### Checks (static/source only)
- `audit_b13_descent.py` exit 0: 15 checks true, including 12 bounded kernel
  decisions, max 58-literal decode, 27 high ids, 57 literal blocks / 1182 ids,
  no high-id intersection, and exact emitter regeneration.
- `audit_b13main.py` exit 0: imports/API/inventory static checks only.
- `audit_next1182_blocks.py` exit 0: 57 blocks, 28 intervals, 1182 ids, manifest
  exactness only.
- `emit_b13_descent_bounds.py` py_compile exit 0; two consecutive emissions both
  produced DescentBounds hash `075B663A...`. `git diff --check` exit 0.
- No local Lean build was run; full-project builds remain CI-only.

### Still unproved / unverified
- DescentBounds, repaired B13, and B13Main remain **CI pending / unpaid**.
  Residual 389, SevenClassExclusions, and the arbitrary-center full-disk
  theorem remain unpaid. Source hashes and audits are not proof credit.

### Next concrete step
- On the first CI run binding `075B663A...`, `3DD37313...`, and `2A6A206F...`,
  require exit 0 in the order DescentBounds, B13, B13Main. If red, use the first
  module-local error; if all green, issue the documented root-import request to
  replace B12Main with B13Main.

## 2026-10-30 - session part 9: bounded source classification

### Done
- Reloaded GUIDANCE/LANES/Lane-B NOTES/CI and ran `project_status.py --check`
  (exit 0; handoff manifest declarations only, not math).
- Diagnosed the red DescentBounds module as kernel deep recursion from one-shot
  `decide +kernel` over image/union definitions. Replaced all 12 decisions with
  structural proofs: the twelve G blocks use `Finset.mem_image.mp` + `fin_cases`;
  B09 is classified through nine explicit union/insert layers, with the four
  image-backed consumers decoded the same way. The 27 high ids and all 57 x 1182
  Next1182 exclusions are byte-preserved in meaning.
- Updated `emit_b13_descent_bounds.py` and extended `audit_b13_descent.py` to
  require 12 G layers, 16 image decodes, nine B09 descent layers, zero kernel
  decisions, exact emitter reproduction, and all previous inventory/exclusion checks.

### Files (SHA256, uppercase)
- `EnergyTerminalBatchB13DescentBounds.lean` `0908F51C58F3D7B187EDC13525C3A25148A2DDC8972BC1AC9D3FD4089FEE5069`.
- `emit_b13_descent_bounds.py` `44D0E336CC2ABA337AF28BA8F9E81A814B0D0EED036A8D3CB78D69E099D9B9B7`.
- `audit_b13_descent.py` `2458A99DE6C4B91CB8A3CB906929CC56EEDE7DA552FF3AB9D52357B86C349FFB`.
- B13 `3DD37313...`, B13Main `2A6A206F...`, TARGETS unchanged.

### Checks (source/static only)
- `audit_b13_descent.py` exit 0: 18 checks true, 16 image decodes, nine B09
  layers, zero `decide +kernel`, 27 high ids, 57 blocks / 1182 Next ids, exact
  emitter reproduction. It also reconstructs all 58 B09 ids from the four packet
  vectors plus the eleven singleton/energy ids and matches the high set exactly.
  `audit_b13main.py` and `audit_next1182_blocks.py` exit 0.
- `audit_b13_closure.py` exit 0 (all 13 inventory counts/checks);
  `audit_target_imports.py` exit 0 (1920-module closure, no missing/forbidden);
  `git diff --check` exit 0.
- Local Lean elaboration was not possible: the Mathlib probe `.olean` tree is
  incomplete (`Mathlib.Data.Finset.Image` absent). This is not a Lean verdict.

### Still unproved / unverified
- DescentBounds, B13, and B13Main remain **CI pending / unpaid**. Residual 389,
  SevenClassExclusions, and the arbitrary-center full-disk theorem remain unpaid.

### Next concrete step
- On the first CI run binding `0908F51C...`, inspect the first module-local
  DescentBounds error (especially any `fin_cases`/`simp` failure) and fix that
  exact step; if it exits 0, proceed to B13, then B13Main and the root-import request.
