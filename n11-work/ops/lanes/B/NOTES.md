# Lane B notes

## 2026-11-01 - session 125: hash-pinned census restoration utility

- Added `restore_census_from_green.py` and its dry-run report. It pins the four
  C01--C04 blobs at green `6937fb90` (SHA-256 `d629d5bc...70499`,
  `ffc9ff2c...a94`, `bc4a9bf4...e697`, `70d5ffd5...ef66b`) and refuses
  `--apply` if any green blob or live `+revert` precondition differs.
- Ran the default read-only mode: `ok=true`, all four green pins match, all
  live files differ from green, and the live `+revert` counts are 13/13/13/12.
  Scope is byte restoration only; it is not a Lean kernel check and pays no
  radius. No lane-C file was changed.
- Next concrete step: supervisor runs
  `python3 n11-work/ops/lanes/B/restore_census_from_green.py --apply`, then CI
  builds lane C/FIRST so the restored census and lane-B structural pair are
  reached before any later heavy target. Inspect the first Lean error.

## 2026-11-01 - session 126: restoration preflight rechecked

- Re-ran `timeout 60s python3 n11-work/ops/lanes/B/restore_census_from_green.py`
  in its default read-only mode. Result `ok=true`, no failures. The pinned green
  commit is `6937fb90`; all four expected SHA-256 values still match the green
  blobs. Live C01--C04 still differ from green and contain 13/13/13/12
  `+revert` markers.
- Scope is byte preflight only, not a Lean kernel check. I did not run
  `--apply`: C01--C04 are lane-C files, outside this lane's write authority.
- No Lean source or target list changed in this session. The `TARGETS.txt`
  structural pair still transitively imports `EnergyTerminalResidualCensus`, so
  reordering targets cannot bypass the conflicted census dependency.
- Next concrete step: supervisor runs
  `python3 n11-work/ops/lanes/B/restore_census_from_green.py --apply`, then
  serially CI `EnergyTerminalResidualCensus`, the lane-B structural pair, and
  inspect the first owning Lean error. Kernel acceptance remains CI pending.

## 2026-11-01 - session 124: CI log attribution and census regression audit

- Downloaded and extracted the full job log for run `41271050741` (job
  `124743726683`, head `5c053c07`). Exit 143 was a runner shutdown, not a Lean
  result. Green exits before shutdown: `EnergyTerminalBatchB13ResidualCertificates`,
  `EnergyTerminalBatchB13RefineSixteenRepair`,
  `EnergyTerminalBatchB13RefineSixteenResidual`, and
  `EnergyTerminalBatchB13RefineSixteenResidualMain` all exited 0.
- The run then started lane C's literal
  `EnergyTerminalBatchB13RefineSixteenResidualCensus`; its dependency build reached
  `EnergyTerminalResidualCensusBase` and then held an approximately 8 GB Lean
  process until runner shutdown. No Lean diagnostic was emitted for that target.
  The lane-B structural consumer was not reached, so it remains **CI pending**.
- Added `audit_census_revert_regression.py` and its JSON report. It compares the
  live four census parts with green commit `6937fb90`. Result `ok=true`, scope
  source/byte audit only: green had 51 bare `decide +kernel` and 0 `+revert`;
  live has 0 bare and 51 `+revert` (13/13/13/12). Live hashes:
  C01 `6E90C8EA...F07F4`, C02 `FC8885BD...C373`, C03 `E1022163...02219`,
  C04 `D40FF05E...F67727`. This is the strongest identified regression blocking
  the census build, but it is not itself a Lean kernel diagnosis.
- Re-ran `audit_structural_residual.py`: `ok=true`, closure 8, no failures.
  Structural SHA256 `6F585404...68B`; StructuralMain `7CE25F5D...4A7`;
  TARGETS `7AE31169...AB`. Both structural modules remain **CI pending** and pay
  no radius.
- Still unproved: kernel success of the structural pair; all 373 residual radii;
  packet `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions (`0/7`);
  arbitrary-centre full-disk theorem.
- Next concrete step: supervisor should not build lane C's literal census first.
  Restore C01--C04 from green `6937fb90` (removing all 51 `+revert`), or withdraw
  that target in favour of the structurally equivalent lane-B wrapper. Then CI
  the four restored census parts, `EnergyTerminalResidualCensus`, lane-B
  `...ResidualStructural`, and `...ResidualStructuralMain` serially. Inspect the
  first owning Lean error; do not infer green from hash or byte checks.
- ROOT-IMPORT REQUEST remains: replace `EnergyTerminalBatchB13Main` with the
  complete green sixteen-refinement main chain only after the structural pair is
  kernel-green.

## Earlier state (condensed)

- CI-green at `6937fb90`: core B13 (1997 paid / 2506 terminal, 120 sharp, 389
  residual), `Refine0037`, Twelve, and singleton dependencies. `B13Main` was
  kernel-green at `521CA436...FA41837`; live root still imports B12Main.
- The repaired sixteen chain reaches 2013 paid / 373 residual conditionally.
  Its interfaces and cardinality wrappers are not radius payments.
- Seven row-cap emitters use exact 700/700 rational arithmetic, but their packets
  do not assert `f0Lo`/`g`. Existing row-cap aliases are green.
- Session 123 rechecked the structural bridge: `Repair.paidIDs` and
  `RefineSixteen.paidIDs` have the same source definition; the native residual
  filters agree. Scope was static source only.
- Session 119 observed the earlier merge left a conflicted literal census module.
  Lane-B's structural wrapper avoids importing that module and proves
  `residualIDs.card = 373` by a 389-census-minus-16 alias.
- Historical ACTIVE/VERIFIED headings and cached verdicts cannot override a
  later qualified handoff. Preserve frozen bytes; only CI exit 0 pays a module.

## Retained engineering facts

- `Finset.card_biUnion` needs explicit disjointness. For `Function.onFun` parts,
  first `change Disjoint (part i) (part j)`.
- Part-local Next1182 lower bounds transfer through the conjunctive bound and
  `omega`; `Finset.disjoint_left.mp` may need `(a := a)`.
- Kernel decisions must stay small and hierarchical. The complete census uses
  four literal chunks and 51 block equivalences.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`, `emit_b13_descent_bounds.py`.
- Audits: `audit_next1182_blocks.py`, `audit_b13_descent.py`,
  `audit_b13main.py`, `audit_b13_closure.py`, `audit_target_imports.py`,
  `audit_b13_refine_{thirteen,fourteen,sixteen}.py`,
  `audit_residual389_crosswalk.py`, `audit_structural_residual.py`,
  `audit_census_revert_regression.py`.
- Workflow success is not a theorem verdict. Only artifact `summary.json` module
  exits or `=== EXIT ... 0` lines count as kernel checks.
- Source/inventory/byte audits and hash matches are not Lean proof credit.

## 2026-11-01 - session 127: independent 373-id census; lane-C dependency removed

- Added deterministic emitter `emit_structural_census.py` and report
  `emit_structural_census-report.json`. It reconstructs the 2506 terminal ids,
  120 sharp ids and 1997 paid ids from checked-in Lean tables plus
  `rest1182-emission-manifest.json`, asserts 389 unconditional residual ids,
  removes the 16 RefineSixteen ids, and asserts four chunks of 100/100/100/73.
- Generated
  `N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.lean`
  (SHA-256 `8EC33EAE...BDB5B`): literal 373-id set, chunk cardinalities,
  pairwise disjointness, `residual373_card = 373`, 51 block-local
  `decide +kernel` set equalities, and `residualIDs_card = 373`. It imports
  only `EnergyTerminalBatchB13RefineSixteenResidual`, not the lane-C census.
- Rewired `EnergyTerminalBatchB13RefineSixteenResidualStructural.lean`
  (SHA-256 `A9EF7A7E...CA0C`) to the new census and placed the new census,
  structural wrapper and structural main ahead of the lane-C census targets in
  `TARGETS.txt` (SHA-256 `31F5A876...C99280`). StructuralMain is unchanged
  (`7CE25F5D...34A7`).
- Checks run: emitter source reconstruction/assertions passed; both
  `audit_structural_residual.py` (`ok=true`, closure 5, lane-C census absent)
  and `audit_target_imports.py` (`ok=true`, closure 1988, no missing/forbidden)
  passed. Scope is source/import/byte audit only; **no Lean kernel check was run**
  and no radius is paid. All three structural modules are **CI pending**.
- Still unproved: kernel success of the three target modules; all 373 residual
  radii; packet `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions
  (`0/7`); arbitrary-centre full-disk theorem.
- Next concrete step: supervisor commits this worktree, then CI runs the
  reordered lane-B targets. Inspect the first Lean error in
  `EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus`; do not claim
  cardinality or structural composition green until CI exit 0. ROOT-IMPORT
  REQUEST remains `...ResidualStructuralMain` only after that.

## 2026-11-01 - session 128: ten-index kernel split; frozen-census cross-check

- Replaced the structural census generator's 100-index `interval_cases`/kernel
  decisions with 502 ten-index `mem_sub_*` facts plus 51 bounded
  `mem_iff_block*` dispatches. Each kernel term now covers at most ten source
  indices and uses closed `Fin 5011` terms after `rcases`, addressing the two
  previously observed failure modes (kernel scale and free-variable `+revert`).
- Added an independent static cross-check: reconstructed 373 ids must equal the
  frozen checked-in 389 chunk union in `EnergyTerminalResidualCensusBase` minus
  the literal 16-id refinement set. This passed, along with 2506 terminal,
  120 sharp, 389 unconditional residual and 373 refined residual counts.
- Regenerated
  `N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.lean`
  (SHA-256 `415C4121...B73A`); emitter SHA-256 `8539B006...8772`. The emitters
  also caught and fixed an intermediate block-cover bug before CI.
- Checks run: deterministic emitter twice with identical output and all
  cross-check assertions; `audit_structural_residual.py` (`ok=true`, closure 5,
  conflicted census absent); `audit_target_imports.py` (`ok=true`, closure 1988,
  no missing/forbidden). Scope is source/import/count audit only: **no Lean
  kernel check**, so all three structural modules remain **CI pending** and no
  radius is paid.
- Still unproved: kernel success of the three target modules; all 373 residual
  radii; packet `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions
  (`0/7`); arbitrary-centre full-disk theorem.
- Next concrete step: supervisor commits this worktree and CI builds the
  structural census first. Inspect the first Lean error in
  `EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus`; only CI exit 0
  can pay cardinality. ROOT-IMPORT REQUEST remains
  `...ResidualStructuralMain` only after the structural pair is kernel-green.

## 2026-11-01 - session 129: regeneration and kernel-risk recheck

- Re-ran `emit_structural_census.py` under a 90 s timeout. It reproduced the
  census byte-for-byte (`415C4121...B73A`) with `count=373`, chunks
  `[100,100,100,73]`, and `base389_crosscheck=true`.
- Re-ran `audit_structural_residual.py` (`ok=true`, closure 5, conflicted
  lane-C census absent) and `audit_target_imports.py` (`ok=true`, closure 1988,
  no missing/forbidden imports). Scope is source/import/byte audit only.
- Static census scan: 5,982 lines, 512 `decide +kernel`, 502 `interval_cases`,
  zero `sorry`/`admit`/`native_decide`/`OfReduceBool`/`implemented_by`/
  `maxHeartbeats 0`; longest generated line 1,903 bytes. These counts do not
  establish kernel success.
- No source changed from session 128; all three structural modules remain
  **CI pending**, and no radius is paid. Still unproved: kernel build of the
  structural census/pair/main; all 373 residual radii; packet `f0Lo`/`g`;
  382 absent payload records; SevenClassExclusions (`0/7`); arbitrary-centre
  full-disk theorem.
- Next concrete step: CI the three structural targets in current order and
  inspect the first owned Lean error. ROOT-IMPORT REQUEST remains
  `...ResidualStructuralMain` only after the structural pair is CI green.
