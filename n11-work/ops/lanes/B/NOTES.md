# Lane B notes

## 2026-11-01 - session 136: exact CI blocker attribution

- Extended `audit_ci_memory.py` to record per-module `✖ ... Building` failures.
  Replaying the downloaded job log for run `41293387736` (head `a90d1ee0`) now
  attributes the failure to exactly C01--C04: all four are killed after 93 s
  with exit 137, while the 13 memory samples peak at 8,755 MiB and the guard
  fires at 387 MiB available. There are zero Lean `error:` diagnostics.
- The log ends with lane C's `...RefineSixteenResidualCensus` exit 1 and then
  attempts its CensusMain; no lane-B structural target is reached. The script
  SHA-256 is `338328E1...752B5`; report SHA-256 is `E0BCB945...BF2F`.
  Scope is CI-log audit only, not a Lean kernel check.
- No Lean source or target list changed. The structural trio remains **CI
  pending** and pays no radius. Still unproved: all 373 residual radii, packet
  `f0Lo`/`g`, 382 absent payload records, SevenClassExclusions (`0/7`), and the
  arbitrary-centre full-disk theorem.
- Next concrete step: replace the structural census's 5,020 direct branch
  decisions (each unfolds the 373/2,013/120-id sets) with a compositional
  terminal-census/cardinality proof, then CI the three targets once C01--C04 are
  restored or withdrawn. ROOT-IMPORT REQUEST remains unchanged until then.

## 2026-11-01 - sessions 133--135 (condensed)

- Import isolation and census-cover audits were green (`ok=true`): the structural
  trio avoids the named lane-C census, but 38 dependencies are shared. Static
  audits are not kernel checks. The trio was moved to the front of
  `B/TARGETS.txt`, yet the global C-first order still blocks it.

## 2026-11-01 - sessions 125--126: hash-pinned census restoration utility

- `restore_census_from_green.py` pins C01--C04 at green `6937fb90` and refuses
  `--apply` on any byte mismatch. Two read-only runs: `ok=true`, all pins match,
  live C01--C04 differ with 13/13/13/12 `+revert` markers. Scope is byte
  preflight only, not Lean; no lane-C bytes changed. `--apply` remains a
  supervisor action.

## 2026-11-01 - session 124: CI log attribution and census regression audit

- Run `41271050741` (head `5c053c07`) shut down without a lane-B Lean result;
  four checked B13 residual dependencies were green. `audit_census_revert_regression.py`
  found the live C01--C04 bytes differ from green `6937fb90` with 51 `+revert`
  markers (13/13/13/12). This is a byte-level regression audit, not a kernel
  diagnosis. Structural targets remained CI pending and paid no radius.

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

## 2026-11-01 - session 130: CI memory failure attribution

- Added `audit_ci_memory.py` (SHA-256 `3C50C8D9...37C36`) and its JSON report
  `audit_ci_memory-report.json` (SHA-256 `90A6A841...D1E`). It resolves a run's
  job from the GitHub API, parses `BUILD`/`EXIT`, memory-sampler and shutdown
  lines, and records whether a Lean diagnostic exists. Scope is CI-log audit
  only, not a Lean kernel check.
- Audited run `41289029262`, head `3cb5d30ed51320efad08c34481bb1fa9aa855afd`.
  Green exits were `EnergyTerminalBatchB13ResidualCertificates`,
  `...RefineSixteenRepair`, `...RefineSixteenResidual`, and
  `...RefineSixteenResidualMain` (all 0). The active target at shutdown was
  lane C's literal `EnergyTerminalBatchB13RefineSixteenResidualCensus`.
- The job's sampler reached 8,627,376 KiB top RSS (Python audit converts this
  to 8,425 MiB) with 1,150 MiB available; then the
  OOM guard fired and the runner shut down (exit 143). There are zero Lean
  `error:` lines. This attributes the failure to memory/shutdown, not a kernel
  rejection of that target.
- Re-ran `restore_census_from_green.py` read-only: `ok=true`; all green blobs
  match commit `6937fb90`, while live C01--C04 remain changed and contain
  13/13/13/12 `+revert` markers. Exact green/live SHA-256 values are in its JSON
  report. I did not run `--apply` because C01--C04 are outside lane-B write
  authority.
- No Lean source or target list changed this session. The lane-B structural
  modules remain **CI pending** and no radius is paid. Still unproved: kernel
  success of the structural census/pair/main; all 373 residual radii; packet
  `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions (`0/7`); the
  arbitrary-centre full-disk theorem.
- Next concrete step: supervisor applies
  `python3 n11-work/ops/lanes/B/restore_census_from_green.py --apply`, confirms
  zero `+revert`, and restarts CI. Inspect the first real Lean error only after
  the restored lane-C dependencies replay/build. ROOT-IMPORT REQUEST remains
  `...ResidualStructuralMain` only after its dependency chain is CI green.

## 2026-11-01 - session 131: CI ordering blocker made executable

- Added `audit_ci_target_order.py` (SHA-256 `821FD134...0916`) and report
  `audit_ci_target_order-report.json` (`AF56DE0C...8241`). It parses the
  workflow's `cat` order and all lane target files. Result `ok=true` for the
  audit and `blocked_before_structural=true`: lane-C's literal
  `...RefineSixteenResidualCensus` is global position 4, while lane-B's
  `...ResidualStructuralCensus` is position 183. The workflow order is C, B, A.
- Re-ran `audit_structural_residual.py`: `ok=true`, closure 5, conflicted
  literal census absent. Structural census/Structural/StructuralMain SHA-256
  are `415C4121...B73A`, `A9EF7A7E...CA0C`, `7CE25F5D...34A7`; no banned token
  occurs in those sources. Scope is static source/import/order audit only.
- This identifies why changing order inside `B/TARGETS.txt` cannot expose the
  new lane-B census: serial CI encounters C's heavy target first. No Lean source
  or target list changed, all three structural modules remain **CI pending**,
  and no radius is paid.
- Still unproved: kernel success of the structural trio; all 373 residual
  radii; packet `f0Lo`/`g`; 382 absent payload records; SevenClassExclusions
  (`0/7`); arbitrary-centre full-disk theorem.
- Next concrete step: supervisor either restores C01--C04 and builds the
  literal census once to completion, or temporarily removes/withdraws that
  lane-C target so CI reaches B position 183. Then inspect the first Lean error
  owned by the structural census. ROOT-IMPORT REQUEST remains
  `...ResidualStructuralMain` only after that dependency chain is CI green.


## 2026-11-01 - session 137: residual cardinality bridge extracted

- Added `EnergyTerminalBatchB13RefineSixteenResidualCard.lean` (49 lines) with
  `terminalIDs := univ.filter terminal`, the extensional identity
  `residualIDs = terminalIDs \ (sharpIDs ∪ paidIDs)`, subset of `sharp ∪ paid`
  in `terminalIDs`, and `residualIDs_card_of_terminal_census`.  The latter
  derives `residualIDs.card = 373` from exactly two remaining premises:
  `terminalIDs.card = 2506` and disjointness of sharp/refined-paid.  This is a
  structural bridge, not a census proof and not a radius payment.
- Registered `N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCard`
  in `ops/lanes/B/TARGETS.txt` immediately after the structural trio.  Status
  is **CI pending**; no kernel claim is made.
- Local check attempt: `lake env lean` from `n11-work/lean` did not reach Lean;
  Lake tried to check out Mathlib revision `0df444a...` over untracked probe
  files and aborted.  Scope was setup failure only, with no Lean diagnostic.
- Still unproved: `terminalIDs.card = 2506`, sharp/refined-paid disjointness,
  kernel success of this bridge and the structural trio, all 373 residual
  radii, packet `f0Lo`/`g`, 382 absent payload records, SevenClassExclusions
  (`0/7`), and the arbitrary-centre full-disk theorem.
- Next concrete step: prove `terminalIDs.card = 2506` from the checked-in
  source-tree structure (or a lane-B-owned hierarchical terminal census), and
  derive sharp/refined-paid disjointness stage-by-stage from
  `EnergyTerminalBatchB13.paid_not_sharp` plus the 16 small refinement deltas;
  then let CI kernel-check the bridge.
