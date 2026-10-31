# Lane B notes

## 2026-10-31 - session 116: census CI-red repair

- CI run `41235435914` (head `791d80b2`) kernel-checked
  `EnergyTerminalBatchB13ResidualCertificates`,
  `...RefineSixteenRepair`, and `...RefineSixteenResidual` at exit 0.
  `...RefineSixteenResidualCensus` then exited 1.
- First owning error: all 51 `mem_iff_blockNN` proofs timed out at `whnf`
  (200000 heartbeats), e.g. line 124 and the whole sequence through 484. The
  tactic `simp [residual373, chunk0, chunk1, chunk2, chunk3]` expanded the
  full union per block. Lines 558/565 also used set equality as a membership
  equality, producing `Eq.mp` type mismatches.
- Added `n11-work/ops/lanes/B/repair_residual373_census.py` and ran it. It
  asserts exactly 51 bounded blocks and 2 rewrites, then changes each block to
  the established `decide +kernel +revert` pattern and each rewrite to a
  membership `simpa`. Check: script self-checks and `git diff --check` pass;
  repaired module is **CI pending** (no local Lean build).
- Still unproved: census/Main kernel success and 373 residual radii; packet
  `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions (`0/7`); and
  the arbitrary-centre full-disk theorem.
- Next: CI the repaired census and `CensusMain`; diagnose the first new error.

## 2026-10-31 - session 115: census partition audit

- Added `n11-work/ops/lanes/B/audit_census_blocks.py` and generated
  `audit_census_blocks-report.json`. It parses all four emitted census parts and
  checks the exact 51-block partition of `Fin 5011`: block `i` is
  `[100*i, min(100*(i+1), 5011))`, there are no gaps or overlaps, every block is
  called once by the assembly, the maximum width is 100, and the final block has
  11 indices. It also reconstructs the four literal chunks and checks sizes
  `100/100/100/89`, pairwise disjointness, and exact equality with lane C's
  389-id census. All ten checks pass (`ok: true`).
- Re-ran the census emitter in regenerating mode and the independent revert
  audit. Counts are still 2506 terminal / 1997 paid / 389 residual; census
  chunks are `100/100/100/89`; the four parts contain `13+13+13+12 = 51`
  `decide +kernel +revert` blocks, zero bare kernel decisions, and no forbidden
  proof escapes. Lean bytes are unchanged from commit `791d80b2`: C01
  `6E90C8EA...F07F4`, C02 `FC8885BD...C373`, C03 `E1022163...02219`, C04
  `D40FF05E...F67727`; assembly `84593DBA...24D6B`.
- Live CI run `41235435914` (head `791d80b2`) reached `Mathlib cache` success and
  is in the build step as of this handoff; there is no kernel verdict yet. The
  new partition audit is static source inspection only and pays no radius.
- Still unproved: kernel success of census C01--C04, assembly and
  `EnergyTerminalResidualCensusRefineSixteen`; 373 refined residual radii;
  packet `f0Lo`/`g`; the 382 absent payload records; SevenClassExclusions
  (`0/7`); and the arbitrary-centre full-disk theorem.
- Next: when run `41235435914` finishes, record the first lane-B-owned build
  error (or green exits), and keep the pending ROOT-IMPORT REQUEST to replace
  `EnergyTerminalBatchB13Main` with `EnergyTerminalBatchB13RefineSixteenMain`
  only after that complete chain is kernel-green.

## 2026-10-31 - session 114: census tactic-hygiene audit

- Added `n11-work/ops/lanes/B/audit_census_revert.py` and generated
  `audit_census_revert-report.json`. It checks the four emitted census parts for
  `decide +kernel +revert` coverage, bare `decide +kernel`, forbidden proof
  escape tokens, the required base import, and SHA256 of every part.
- Check passed: exactly `13+13+13+12 = 51` revert blocks, zero bare kernel
  decisions, zero forbidden tokens, all four part hashes equal the emitter
  report. Scope: Python source audit only; this does **not** kernel-check Lean
  and does **not** pay any radius.
- Confirmed from installed Mathlib source that `decide +revert` is supported,
  but the attempted local `Mathlib`-import probe exceeded its 120 s timeout with
  no result; do not count it as a Lean check. The repaired `C01`--`C04` remain
  **CI pending**.
- Still unproved: kernel success of the repaired census/assembly, 373 refined
  residual radii, packet `f0Lo`/`g`, the 382 absent payload records,
  SevenClassExclusions (`0/7`), and the arbitrary-centre full-disk theorem.
- Next: supervisor commit, then serial CI of `C01`--`C04`, assembly, and
  `EnergyTerminalResidualCensusRefineSixteen`; diagnose the first owning error.

## 2026-10-31 - session 113: final census crosswalk validation

- Re-read run-67 artifact: lane-B census `C01`--`C04` repair is still **CI pending**.
  The red `EnergyTerminalBatchB13RefineSixteenResidualCensus` is lane C's target
  (line 41 extra `decide`, line 50 free subtype variables), not lane-B-owned.
- Re-ran the lane-B census emitter in check mode and the independent crosswalk.
  Exact results: 2506 terminal, 1997 paid, 389 residual; chunks `100/100/100/89`;
  `13/13/13/12 = 51` `decide +kernel +revert` blocks; 389 lane-B ids match all
  389 lane-C census entries; 7 local survey records, 382 absent.
  Crosswalk ids SHA256 `747447E2...07F46`.
- Regenerated-byte hashes unchanged: C01 `6E90C8EA...F07F4`, C02
  `FC8885BD...C373`, C03 `E1022163...02219`, C04 `D40FF05E...F67727`;
  assembly `84593DBA...24D6B`; report input `D0588829...8A6BBD`.
- Scope: Python exact-source checks only. No project Lean build was run
  (2-core rule), so kernel status remains **CI pending**. No radius is paid.
- Still unproved: 373 refined residual radii, packet `f0Lo`/`g`, the 382 absent
  payload records, SevenClassExclusions (`0/7`), and the arbitrary-centre
  full-disk theorem.
- Next: supervisor commit and serial CI of C01--C04, assembly, then
  `EnergyTerminalResidualCensusRefineSixteen`; diagnose the first owning error.
  Keep the SixteenMain root-switch request.

## 2026-10-31 - session 112 (condensed)

- Confirmed run `41222715534` completed successfully and both
  `FrozenCapFiveField{2368,2370}Tree` aliases are kernel-green there.
- Removed consumer-free `LaneBUnpaidPublicExcludedWrappers.lean` and its target.
- Repaired the lane-B 389 census emitter to emit `decide +kernel +revert`,
  preventing free subtype `hk` in interval-case blocks. Output remains CI pending.
- `LaneBPublicResidualCrosswalk` records that exactly seven public row-cap ids
  occur among the 389 residual ids; exactly `{2337,2341}` occur among the 16
  refinements, so five `{1409,2356,2360,2368,2370}` remain in the literal 373.
  Bookkeeping only; **CI pending**; pays no radius.

## Earlier state (condensed)

- Core B13 is CI-green at `6937fb90`: 1997 paid / 2506 terminal, 120 sharp,
  389 residual. `Refine0037`, Twelve, and singleton dependencies were CI-green
  at `cc04268c`. Sixteen reaches conditionally 2013 paid / 373 residual.
- `B13Main` is kernel-green at `521CA436...FA41837`. Live root still imports
  B12Main. ROOT-IMPORT REQUEST: replace `EnergyTerminalBatchB13Main` with
  `EnergyTerminalBatchB13RefineSixteenMain` when the complete chain is green;
  supervisor-only, and this switch cannot by itself pay any residual radius.
- Seven row-cap emitters have exact 700/700 rational arithmetic, but their
  packets cannot assert `f0Lo`/`g`. Existing row-cap aliases are green.
- Preserve frozen bytes. Historical status/cached verdicts do not pay proofs.

## Retained engineering facts

- `Finset.card_biUnion` needs explicit disjointness. For `Function.onFun` parts,
  first `change Disjoint (part i) (part j)`.
- Part-local Next1182 lower bounds transfer through the conjunctive bound and
  `omega`; `Finset.disjoint_left.mp` may need `(a := a)`.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`, `emit_b13_descent_bounds.py`.
- Audits: `audit_next1182_blocks.py`, `audit_b13_descent.py`,
  `audit_b13main.py`, `audit_b13_closure.py`, `audit_target_imports.py`,
  `audit_b13_refine_{thirteen,fourteen,sixteen}.py`,
  `audit_residual389_crosswalk.py`.
- Workflow success is not a theorem verdict. Only artifact `summary.json`
  module exits or `=== EXIT ... 0` lines count as kernel checks.
- Source/inventory/byte audits and hash matches are not Lean proof credit.
