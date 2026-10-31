# Lane B notes

## 2026-10-31 - session 71: row-cap leaves switched to kernel decision (CI pending)

- Session 70's bounded Mathlib probe could not be reproduced locally: `lake
  env lean` hung under the shared 2-core workload and was killed at 240 s with
  no diagnostic. This is an infrastructure timeout, not a syntax/kernel result.
- Updated `n11-work/ops/lanes/B/split_rowcap_modules.py` SHA256
  `4808F603...B0543B` to emit exact leaf proof `decide +kernel`; theorem
  statements, `dbmVal`, and aggregate `row_cap` dispatch are unchanged.
- Regenerated all seven `LaneBFrozenCapRowCap*.lean` modules: 700 leaves total,
  exact `Fraction` caps all pass (`7 x 100` pairs, each `y` sum `1`, zero
  violations). Module SHA256: `1409 4F1D8B5D...8F12`, `2337
  73E0B6EF...29A4`, `2341 FB652D1D...52DD`, `2356 16BB8063...B9F7`, `2360
  C25D85D4...2B58`, `2368 5C8272EE...80D7`, `2370 84AB5449...4777`.
- New exact-arithmetic/regeneration report:
  `split_rowcap_modules-report-new.json` SHA256 `49828C87...9130C`.
  `split_rowcap_modules.py --check` exits `0`; `py_compile` and
  `git diff --check` exit `0`; forbidden-construct scan has no matches.
  Scope is source/inventory/rational arithmetic only. Every changed cap module
  remains **CI pending**; none is kernel proof credit until its own exit `0`.
- TARGETS order puts `LaneBRowCapDecideProbe` immediately before the seven cap
  modules, so fresh CI isolates representative `decide +kernel` leaves first.
- Still unproved: kernel exits for the probe, all seven 100-row modules and
  public excluded tree; all 373 residual radii; the `f0Lo`/`g` bridge;
  SevenClassExclusions (`0/7`); arbitrary-center full-disk theorem.
- Next: supervisor commits these exact bytes unchanged, then CI must report the
  probe and `LaneBFrozenCapRowCap1409` exits separately. If green, audit 2356;
  if red, use the first probe/1409 source diagnostic to select the next leaf
  shape before touching the already regenerated other modules.

## 2026-10-31 - session 70: row-cap tactic regression isolated; kernel probe queued

- Re-ran `python tools/project_status.py --check`: PASS (handoff declarations only).
  Banked the uncommitted Fourteen alias repair (`d1b84824...aba58dc`), whose
  static successor hash now matches the fresh CI diagnosis.
- Fresh run `41150468008` confirms `RefineThirteen` and `ThirteenMain` exit `0`;
  the first repair failure is Fourteen's local-`newIDs` rewrite, now fixed on
  disk. Fourteen/FourteenMain/Sixteen/SixteenMain remain **CI pending**.
- Diagnosed the seven `LaneBFrozenCapRowCap*` red targets from that same artifact.
  `FrozenCapRowCap1409` emits `unsolved goals` at each cap theorem declaration.
  Exact Python/Q rational recomputation checks all `100` node-1409 rows,
  `y` sum `1`, minimum slack `0`; the caps are true, so this is a tactic failure.
- The lane-B split emitter still emits the old
  `norm_num [y_1409, rowA, db, dbmVal]`; lane C changed the emitter but its own
  modules are still CI-red with `norm_num [rowA] <;> norm_num [y_1409, db]`.
  Reproducing lane C's change is therefore not a repair.
- Added `LaneBRowCapDecideProbe.lean` (SHA256 `268043a2...40687b`) with three
  representative caps (`0,1`, `4,5`, `9,9`) proved by `decide +kernel`, plus
  `LaneBRowCapDecideProbe` in `TARGETS.txt` (SHA256 `05e2a0dc...b9d3`).
  This is **drafted, CI pending**, not proof credit and not a 100-row certificate.
- Checks: `audit_b13_refine_sixteen.py` exit `0` (all static checks pass, 2013
  paid / 373 residual); `audit_target_imports.py` exit `0` (closure `1966`, no
  missing/forbidden imports, probe resolved); `git diff --check` exit `0`.
  Scope is static source/inventory/rational arithmetic and import resolution.
- Still unproved: all 373 residual radii, the `f0Lo`/`g` bridge,
  SevenClassExclusions (`0/7`), all seven 100-row cap modules, and the
  arbitrary-center full-disk theorem.
- Next concrete step: fresh CI must separately report exit `0` for the probe,
  Fourteen, FourteenMain, Sixteen and SixteenMain. If the probe is green, change
  `split_rowcap_modules.py` to emit kernel-decision leaves (or the smallest
  green proof shape), regenerate all seven modules, and rerun exact 700/700
  rational checks; if red, inspect the first probe diagnostic and use it to
  choose the next proof shape. Never infer success from the run-level status.

## 2026-10-31 - session 69: fresh CI isolates Fourteen alias failure and repair

- Read fresh run `41150468008` on `24e434b4` (artifact `13024663395`, SHA256
  `93bd13b7...c1b98`). It proves the previous repair: `RefineThirteen` and
  `RefineThirteenMain` both exit `0`.
- The next real diagnostic is `RefineFourteen.lean:62:53`: `paid_count` rewrites
  `new_count`, but `paidIDs` unfolded to `EnergyRefineN3116.newIDs`, leaving
  `2010 + #EnergyRefineN3116.newIDs = 2011`. Fixed the definition to
  `RefineThirteen.paidIDs ∪ newIDs`. The four `FourteenMain`, `Sixteen`, and
  `SixteenMain` exits are dependency cascades with no independent errors.
- Re-ran `audit_b13_refine_sixteen.py`: exit `0`, all checks including the new
  `fourteen_paid_ids_use_alias` guard; `audit_b13_refine_thirteen.py`: exit `0`.
  `git diff --check`: exit `0`. A first 90s `audit_target_imports.py` attempt
  timed out; the bounded 180s rerun exits `0` with closure `1965`, no missing or
  forbidden imports. This remains static import-resolution scope.
- Exact repaired Fourteen SHA256 `d1b84824...ba58dc`; audit script
  `5c54c82e...25f3b2`; audit report `d83093fb...39acb4`. Fresh CI evidence is in
  `ci-verdict-41150468008.json`. All readings are static/artifact scope; none is
  Lean proof credit for the new bytes.
- Still unproved: all 373 residual radii, the `f0Lo`/`g` bridge,
  SevenClassExclusions (`0/7`), and the arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits/pushes the alias repair unchanged; fresh
  serial CI must report exit `0` separately for all four `Fourteen`/`Sixteen`
  targets before root integration. If another error appears, start from its exact
  first diagnostic.

## 2026-10-31 - session 68: handoff byte/hash recheck (condensed)

- Static six-target gate passed (`2013` paid, `373` residual, import closure
  `1965`); no new Lean/kernel credit. The old overall-green CI was false at
  module level; post-repair Thirteen/Fourteen/Sixteen remained CI pending.

## 2026-10-31 - session 64: CI artifact exposed and repaired Thirteen

- `python tools/project_status.py --check` passed. Starting tree was clean at
  merged `HEAD c63cb61e`; the previously "CI-pending" Thirteen/Fourteen/Sixteen
  bytes are now committed.
- Fetched GitHub run `41141569628` (`n11-lean-build`, head `c63cb61e`, overall
  success) and inspected artifact `13021186040`
  (`n11-build-41141569628.zip`, 26047 bytes, SHA256 `AAAA0E3D...E54CCE`). The
  run-level success is a false green: the workflow's trailing `true` masks
  module exits.
- Artifact `summary.json` records exit `1` for `RefineThirteen`,
  `ThirteenMain`, `RefineFourteen`, `FourteenMain`, `RefineSixteen`, and
  `SixteenMain`. The first Lean error is
  `EnergyTerminalBatchB13RefineThirteen.lean:65:2: No goals to be solved`.
  Therefore none of the 2013-paid / 373-residual chain had kernel proof credit
  at that commit, despite the green run.
- Repaired `EnergyTerminalBatchB13RefineThirteen.lean` by removing the redundant
  `norm_num` after the preceding `rw` closed `twelve_new_count`. New SHA256 is
  `F62B93EB0B60B812CB30767A745CCD2D57C197269D1E78A8C2B0CBFCC9E9252E`;
  pre-repair SHA256 was `FE498E4D...A690E739`.
- Added `ci-verdict-41141569628.json` to preserve the artifact identity, exact
  six module exits, first diagnostic, and pre/post-repair hashes. Its
  `post_repair_ci` field is explicitly `pending`.
- Checks after the repair: `audit_b13_refine_thirteen.py`,
  `audit_b13_refine_fourteen.py`, and `audit_b13_refine_sixteen.py` all exit 0
  with `ok:true`; `audit_target_imports.py` exits 0 with a 1965-module closure;
  `py_compile` and `git diff --check` exit 0. These are static
  source/inventory checks only, not Lean elaboration or proof credit.
- The chain arithmetic remains conditionally `2013` paid, `389 - 16 = 373`
  residual. Files involved are `EnergyTerminalBatchB13RefineThirteen.lean`
  (`F62B93EB...E9252E`), `ThirteenMain` (`D46E758C...D2784375`), `Fourteen`
  (`12D107B3...DD0E4`), `FourteenMain` (`9478C19F...C3FE7`), `Sixteen`
  (`055F8BA3...C28851`), `SixteenMain` (`A3103831...8FECF`), and
  `TARGETS.txt` (`69E4E5A5...9F612`).
- Still unproved: the conditional 373 residual radii themselves, the `f0Lo`/`g`
  bridge, SevenClassExclusions (`0/7`), and the arbitrary-center full-disk
  theorem. Row-cap targets remain CI-red and do not pay a residual radius.
- Next concrete step: supervisor commits the repaired Thirteen and this evidence
  file unchanged, then requires fresh serial CI module exits `0` for
  Thirteen, ThirteenMain, Fourteen, FourteenMain, Sixteen and SixteenMain. If
  green, the supervisor-only root switch from `B13Main` to `SixteenMain` can be
  reconsidered; the root is not imported by this lane.

## Earlier 2026-10-30 work (condensed)

- Core B13 is CI-green at `6937fb90`: 1997 paid of 2506 total, 120 sharp, 389
  residual. `Refine0037`, Twelve and singleton dependencies are CI-green at
  `cc04268c`. The 16 singleton refinements reach conditionally 2013 paid / 373
  residual, but session 64 showed the final chain bytes were CI-red.
- Prior chain repairs: fixed the 0037 `next505_lt` exclusion bug; split
  image/union layers in DescentBounds; corrected the 27-id B09 classification;
  removed duplicate Fourteen -> TwentyTwo -> TwentyFour aggregation; restored a
  unique `7+1+3+1+1+1+2 = 16` singleton chain.
- B13Main is kernel-green at `521CA436...FA41837`. The live root still imports
  B12Main; the requested handoff is supervisor-only and does not reduce the 389
  (now conditionally 373) residual arithmetic by itself.
- `audit_residual389_crosswalk.py` matched all 389 lane-C census entries; only
  seven have local records, all `pass_recorded=false`. Seven row-cap emitters
  have exact 700/700 rational arithmetic but their Lean targets are red on
  unsolved leaves and cannot force `f0Lo`/`g`.

## Retained engineering facts

- `Finset.card_biUnion` takes disjointness explicitly. For
  `Function.onFun` parts, use `change Disjoint (part i) (part j)` first.
- Part-local Next1182 lower bounds transfer globally through the conjunctive
  bound plus `omega`; `Finset.disjoint_left.mp` may need `(a := a)`.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`, `emit_b13_descent_bounds.py`.
- Audits: `audit_next1182_blocks.py`, `audit_b13_descent.py`,
  `audit_b13main.py`, `audit_b13_closure.py`, `audit_target_imports.py`,
  `audit_b13_refine_{thirteen,fourteen,sixteen}.py`.
- Workflow run success is not a theorem verdict. Only the artifact
  `summary.json` module exits or `=== EXIT ... 0` lines count as kernel checks.
- Source/inventory/byte audits and hash matches are not Lean proof credit.

## Session 22-23 (condensed)

B13Main was kernel-green at `521CA436...FA41837`; root imports B12Main. Evidence
is in `ci-b13-green-20261030.json`.

## 2026-10-31 - session 72: local probe infrastructure blocked; CI gate unchanged

- Re-ran `python tools/project_status.py --check`: PASS (handoff declarations
  only). Working tree still contains session-71 exact regenerated cap modules,
  probe, Fourteen alias repair, and pending target/notes changes.
- Re-ran `split_rowcap_modules.py --check` and `py_compile`: exit `0`; exact
  check again covers all `7 x 100` ordered pairs, `y` sums `1`, zero violations.
  This remains rational-arithmetic/source scope, not Lean elaboration.
- Local project probe attempt (`lake env lean LaneBRowCapDecideProbe.lean`) was
  killed at 100 s while `lake` was still cloning Mathlib; no Lean diagnostic.
  A second bounded Mathlib-only probe attempt hit the same 90 s timeout before
  elaboration. These are infrastructure timeouts, not success or tactic failure.
- `git diff --check` exits `0`; forbidden-construct scan finds only the intended
  `decide +kernel` leaves in the probe/cap modules. No frozen module was edited.
- Cap module SHA256 unchanged from session 71 (`1409 4F1D8B5D...8F12`, `2337
  73E0B6EF...29A4`, `2341 FB652D1D...52DD`, `2356 16BB8063...B9F7`, `2360
  C25D85D4...2B58`, `2368 5C8272EE...80D7`, `2370 84AB5449...4777`).
- All seven cap modules and probe remain **CI pending**. The exact 700-row
  arithmetic does not pay the `f0Lo`/`g` bridge or any residual radius.
- Next: supervisor commit unchanged; fresh CI must first report the probe and
  1409 separately. Do not regenerate other modules until that diagnostic exists.

## 2026-10-31 - session 73: static gates fresh; tactic probe still infrastructure-blocked

- Re-ran `python tools/project_status.py --check`: PASS (handoff declarations
  only). Working-tree inventory is unchanged from session 72: probe, seven
  exact regenerated row-cap modules, Fourteen alias repair, and pending
  target/report updates are present.
- `split_rowcap_modules.py --check` exits `0` and independently reports all
  `7 x 100` ordered pairs, `y` sum `1`, zero violations. Regenerated module
  hashes remain `1409 4F1D8B5D...8F12`, `2337 73E0B6EF...29A4`, `2341
  FB652D1D...52DD`, `2356 16BB8063...B9F7`, `2360 C25D85D4...2B58`, `2368
  5C8272EE...80D7`, `2370 84AB5449...4777`.
- `audit_b13_refine_sixteen.py` exits `0`: final arithmetic is `2013` paid /
  `373` residual, with all static source/inventory checks true. Scope is static
  arithmetic only, not Lean proof credit.
- `audit_target_imports.py` was bounded at `25 s` and timed out with no output;
  the last completed static closure remains the session-72 hash-bound report.
- A minimal Mathlib-only `decide +kernel` rational probe
  (`/workspace/tools/mathlib-probe/RatDecideKernelProbe.lean`) timed out at `45 s`
  before elaboration. No success, failure, or tactic verdict is inferred.
- Probe SHA256 remains `268043a2...40687b`; `TARGETS.txt` SHA256 remains
  `05e2a0dc...b9d3`, with the probe immediately before the seven cap modules.
  All probe/cap targets remain **CI pending**.
- Still unproved: kernel exits for the probe and seven cap modules; the `f0Lo`/`g`
  bridge; all `373` residual radii; SevenClassExclusions (`0/7`); the
  arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits these exact bytes unchanged. Fresh CI
  must first report `LaneBRowCapDecideProbe` and `LaneBFrozenCapRowCap1409`
  exits separately; if probe is `0` and 1409 is `1`, use its first source
  diagnostic to redesign only 1409's leaves, not the other six modules.
