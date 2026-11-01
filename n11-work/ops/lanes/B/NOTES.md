# Lane B notes

## 2026-11-01 - session 123: bridge source recheck; CI remains sole gate

- Re-ran `audit_structural_residual.py`: `ok=true`, depth-2 closure of 8
  modules, no failures; hashes unchanged at Structural
  `6F585404...68B`, StructuralMain `7CE25F5D...4A7`, TARGETS
  `7AE31169...AB`. `git diff --check` was clean in session 122.
- Directly compared both paid-set definitions again: `Repair.paidIDs` and
  `RefineSixteen.paidIDs` each elaborate to
  `RefineFourteen.paidIDs ∪ newIDs`, with the same two-element `newIDs`.
  The residual filters are identical. This supports the `rfl` bridge but is
  source evidence only.
- Scope: static source inspection plus bounded Python audit. No Lean build was
  run locally; neither structural target has kernel credit. CI `41266567914`
  ended in runner shutdown (143), not a Lean diagnosis.
- Still unproved: kernel success of the structural pair; all 373 residual
  radii; packet `f0Lo`/`g`; 382 absent payload records;
  SevenClassExclusions (`0/7`); arbitrary-centre full-disk theorem.
- Next: supervisor commit, then serial CI of
  `EnergyTerminalBatchB13RefineSixteenResidualStructural` followed by its
  `...Main`. If red, inspect the first owning Lean error before changing the
  definitional bridge; if green, retire the conflicted literal census target.


## 2026-11-01 - session 120: structural wrapper wiring audit

- Added `audit_structural_residual.py` and report; pass covers imports,
  endpoints, banned tokens and exact hashes. Structural source hash
  `6F5854043CE50E40DD8E9448ADD703A7BDA095DCA56BF97D17CA8BF9D87CE68B`; main `7CE25F5DF035E68DE463561E589A674B793386369FDCF81FA0378BB995FC34A7`; targets `7AE311698D0910990C9F68C15CC0BBF37C46B156AA24322487FD8236A4E8D5AB`.
- Both structural modules are **CI pending**; no Lean build and no radius paid.

## 2026-11-01 - session 119: structural census isolates merge regression

- Inspected `HEAD da346970` after CI `41266567914` (runner shutdown, exit 143,
  no Lean error). The merge left
  `EnergyTerminalBatchB13RefineSixteenResidualCensus.lean` uncompilable: it
  has duplicate `residual373` declarations and references undefined
  `chunk0`--`chunk3`. The earlier red run `41248242451` confirms the old
  literal-census failure, while `RefineSixteenResidualMain` was green there.
- Left lane C's contested file untouched. Added lane-B-owned
  `EnergyTerminalBatchB13RefineSixteenResidualStructural.lean` and
  `...ResidualStructuralMain.lean`. They use the 389-census-minus-16 structural
  alias, prove `residualIDs_card = 373`, and expose four conditional
  certificate/producer to arbitrary-centre endpoints with seven classes and all
  373 radii still explicit.
- Added both modules to `n11-work/ops/lanes/B/TARGETS.txt` after their upstream
  imports. Checks passed (scope: static/source only): 2 unique targets, all
  imports resolve, no `sorry`/`admit`/`native_decide`/`ofReduceBool`/
  `implemented_by`, no literal `chunk*` or `decide +kernel`, four main endpoints,
  and `git diff --check` clean.
- SHA256: Structural `6F5854043CE50E40DD8E9448ADD703A7BDA095DCA56BF97D17CA8BF9D87CE68B`;
  StructuralMain `7CE25F5DF035E68DE463561E589A674B793386369FDCF81FA0378BB995FC34A7`;
  TARGETS `7AE311698D0910990C9F68C15CC0BBF37C46B156AA24322487FD8236A4E8D5AB`.
- Scope is engineering only: **CI pending**, no Lean build run locally, no
  radius paid. Still unproved: 373 radius certificates; packet `f0Lo`/`g`;
  382 absent payloads; SevenClassExclusions (`0/7`); arbitrary-centre theorem.
- ROOT-IMPORT REQUEST unchanged: switch to `RefineSixteenMain` only after a
  complete green chain. Very next step: supervisor commit, then CI the two
  Structural targets first; if they pass, retire the conflicted literal target
  rather than restoring its per-index kernel enumeration.

## 2026-10-31 - session 118 (condensed)

- Literal 373-census repair remains **CI pending**; the later merge conflicted
  that module. Use the structural replacement rather than re-enumerating it.

## 2026-10-31 - session 117b: repair-partition verification

- Re-read CI `41229638083`: `RefineSixteenResidualCensus` and its `Main`
  remain red at that SHA; the source repair from session 117 is newer and
  **CI pending**, so it is not claimed green.
- Re-ran the partition audit: 51 closed-term `change`s, exact
  `100/100/100/73` range/no-gap partition; source SHA `91F7F7ED...EF658`.
  No Lean check; the literal census is superseded by the structural wrapper.
- Still unproved: kernel success of the repaired census and `Main`; 373
  residual radii; packet `f0Lo`/`g`; 382 absent payload records;
  SevenClassExclusions (`0/7`); the arbitrary-centre full-disk theorem.
- Very next step: supervisor commit, then CI of the repaired census and
  `...CensusMain`; inspect the first owning error before further edits.

## 2026-10-31 - session 117: census free-variable repair

- CI run `41229638083` gave the owning error for
  `EnergyTerminalBatchB13RefineSixteenResidualCensus` at line 49:
  `Expected type must not contain free variables`, repeated for every member
  of the first 100-index block. The cause is the proof field `hk` retained in
  `⟨k, hk⟩` after `rcases`, not a false residual membership.
- Added `n11-work/ops/lanes/B/repair_census_free_vars.py` and repaired all 51
  blocks in `EnergyTerminalBatchB13RefineSixteenResidualCensus.lean`: each
  case now `change`s to the propositionally equal closed term
  `⟨k, by decide⟩`, then rewrites the residual-census equivalence and runs
  `decide +kernel`. Removed all 51 `+revert` modifiers.
- Checks: `repair_census_free_vars.py --check` confirms 51 blocks, 102 closed
  `Fin.mk` occurrences, zero `+revert`; the static forbidden-token scan finds
  no `sorry`, `admit`, declaration `axiom`, `native_decide`, `ofReduceBool`, or
  `implemented_by`; `py_compile` and `git diff --check` pass. Scope is source
  shape only: **CI pending**, no Lean elaboration locally. A core-only
  proof-irrelevance probe was attempted but timed out under worker contention
  and is not counted.
- Census source SHA256:
  `91F7F7ED65FDADD45CA6057F567C61831B2BE12D4F865B02276573478C7EF658`;
  repair script SHA256:
  `1334B6D61B8D5284BC15F1361E601081C846CA1ED649A4ECBB42089E8E1D52E9`.
- Still unproved: kernel success of the 373 census/assembly/Main; 373 residual
  radii; packet `f0Lo`/`g`; 382 absent payload records;
  SevenClassExclusions (`0/7`); the arbitrary-centre full-disk theorem.
- Next: CI `RefineSixteenResidualCensus` and `...CensusMain`; if still red,
  read the first new error before changing the mathematical census.

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
