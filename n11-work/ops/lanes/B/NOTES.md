# Lane B notes

## 2026-10-31 - session 79: bounded local verification of row-cap repair

- Re-read GUIDANCE, lane B, NOTES and `ci/LATEST.md`. `project_status.py --check`
  exits `0` (manifest index only, not proof or full-file integrity).
- Confirmed the current repair shape in all seven row-cap modules: `100` leaf
  declarations and `100` direct `norm_num [y_<node>, rowA, db, dbmVal]` proofs
  per module, with zero `change` steps. `split_rowcap_modules.py --check`,
  `py_compile`, `git diff --check` and the forbidden-token scan all exit clean;
  exact arithmetic remains `700/700`, weight sums `1`, zero violations.
- Local Lean is still unavailable: `lake env lean` tries to check out Mathlib
  revision `0df444a3` and aborts because the package tree is incomplete; the
  Mathlib probe also timed out (`30 s`). Therefore there is **no local Lean
  verdict** and all seven caps plus probe remain **CI pending**.
- Exact hashes: emitter `9EF7286A...A706`; probe `D48FFDA1...824D5`.
  This session changed no Lean bytes; it only strengthens the static verdict.
- Still unproved: kernel exits for probe, seven row caps and public excluded
  tree; 373 residual radii; `f0Lo`/`g` bridge; SevenClassExclusions (`0/7`);
  arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits/pushes these exact bytes. Fresh serial
  CI must report `LaneBRowCapDecideProbe` first; repair only the first new Lean
  diagnostic there, then inspect `LaneBFrozenCapRowCap1409` before the other six.

## 2026-10-31 - session 78: remove definitional `change` leaves

- Latest CI `41168580187` is on older commit `0f022bfb`, not the lane bytes in
  this worktree. It confirms the previous row-cap leaves fail at `change`
  (`LaneBFrozenCapRowCap1409.lean:121` onward), because the closed rational
  and the `y`/`rowA`/`db` expression are arithmetically equal, not definitionally
  equal. The probe itself was green (`LaneBRowCapDecideProbe` exit `0`).
- Changed `split_rowcap_modules.py` to emit
  `norm_num [y_<node>, rowA, db, dbmVal]` for every leaf, removing all 700
  `change` steps. Applied the same tactic to the three probe leaves in
  `LaneBRowCapDecideProbe.lean`; regenerated all seven
  `LaneBFrozenCapRowCap*.lean` modules.
- `split_rowcap_modules.py --check`, `py_compile`, forbidden-token scan, and
  `git diff --check` exit `0`; exact checks remain 7 nodes, 700/700 caps,
  weight sums `1`, zero violations. New SHA256: emitter
  `9ef7286a...a706`; caps 1409 `41B667E8...EB83`, 2337
  `5B64C0F3...4973`, 2341 `4387B181...0F9A`, 2356 `38C519FD...7376`, 2360
  `04404AB7...3F43`, 2368 `6067F76D...6C6D`, 2370 `D0458CBE...D287`.
- `project_status.py --check` exit `0` (manifest only). Local Mathlib probe
  could not run: its Mathlib oleans are absent and a trivial `lake env lean`
  test timed out before Lean started, so there is **no local Lean verdict**.
  `audit_target_imports.py` timed out at 60 s (exit `124`), so no fresh closure
  verdict. All seven repaired caps and the probe are **CI pending**.
- Still unproved: kernel exits for probe/caps/B13 chain/public excluded tree;
  373 residual radii; `f0Lo`/`g` bridge; SevenClassExclusions (`0/7`); the
  arbitrary-center full-disk theorem.
- Next: supervisor commits these bytes; fresh serial CI must start with probe,
  1409, 2337. If the direct `norm_num` leaves are red, repair from that first
  exact diagnostic; if green, finish fresh exits for Fourteen/Sixteen and then
  request the supervisor root switch.

## 2026-10-31 - sessions 70--71 (condensed)

Fresh run `41150468008` was kernel-red only at each row-cap leaf (`unsolved
goals`) and at Fourteen's local `newIDs` rewrite; Thirteen/Main were green.
The seven exact `Fraction` caps were 700/700 true. Session 70 added a
three-leaf probe; session 71 changed the emitter to `decide +kernel` and
regenerated all seven modules (700 caps, zero violations), but neither had a
Lean verdict. Local Mathlib/project probes timed out before elaboration.

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

## 2026-10-31 - session 74: exact-rational leaves replace kernel decision

- `decide +kernel` could not unfold the ordinary `y`, `rowA`, `db`, and
  `dbmVal` definitions in generated leaves. Changed the lane-B emitter
  `split_rowcap_modules.py` to emit, for every leaf,
  `change <exact-lhs> ≤ <exact-rhs>` followed by `norm_num`.
- Regenerated all seven `LaneBFrozenCapRowCap*.lean` modules: 100 explicit
  leaves each. The probe now mirrors the real failure path, including `dbmVal`
  and `db`, for pairs `(0,1)`, `(4,5)`, `(9,9)`.
- Static checks: `project_status.py --check` exit `0` (manifest only);
  emitter `--check` exit `0`, `py_compile` exit `0`, `git diff --check` exit
  `0`; 700/700 leaf count, exact arithmetic 700/700, `y` sums `1`, zero
  violations, forbidden-token scan empty. `audit_target_imports.py` timed out
  at 60 s, so no fresh closure verdict. None of this is Lean proof credit.
- SHA256: emitter `b9523b3d...35ef`, report `8446ac32...55f0`, targets
  `eb52f2b4...dd01`, probe `0087c440...10f0`; cap modules `1409
  0e020af7...b5e2`, `2337 93bae1e0...09a9`, `2341 151e4013...1906`, `2356
  fd53b2db...9064`, `2360 c060e5e1...4e4`, `2368 35cf9bda...c599`, `2370
  45bf9020...12e4`.
- TARGETS now runs the probe and seven row caps before the B13 chain. All
  changed modules are **CI pending**. Still unproved: kernel exits for probe,
  seven row caps and public excluded tree; 373 residual radii; `f0Lo`/`g`
  bridge; SevenClassExclusions (`0/7`); arbitrary-center full-disk theorem.
- Next: supervisor commits unchanged, then fresh CI's first rows must be probe,
  1409, 2337. If probe is red, use its first `change`/`norm_num` diagnostic;
  if green, inspect 1409 before trusting the other six.## 2026-10-31 - session 80: local probe unavailable; exact pending-CI handoff

- Re-read GUIDANCE, LANES, this NOTES and `ci/LATEST.md`. Latest recorded CI
  `41168580187` is still on `0f022bfb`, so it predates the current repaired
  row-cap bytes and does not test the `norm_num [y, rowA, db, dbmVal]` leaves.
- The local Mathlib cache is present, but both `FrozenCapProbe.lean` and a
  narrower rational/Fin probe exceeded a bounded `90 s`/`60 s` elapsed limit
  before any Lean diagnostic. No local Lean verdict; do not infer success.
- Re-ran `split_rowcap_modules.py --check`: exit `0`, seven nodes, 100 leaves
  each, exact arithmetic and weight sums still valid with zero violations.
  Forbidden-token scan over probe + seven caps + emitter is empty. These are
  static checks only, not kernel proof credit.
- Exact current hashes: probe `D48FFDA1...824D5`, 1409 `41B667E8...EB83`,
  emitter `9EF7286A...A706`; the other six caps match the session-79 hashes in
  the `--check` output. This session changed no Lean bytes.
- Still unproved: all eight row-cap/probe kernel exits (CI pending), 373
  residual radii, the `f0Lo`/`g` bridge, SevenClassExclusions (`0/7`), and the
  arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits/pushes these exact bytes unchanged.
  Fresh CI must report `LaneBRowCapDecideProbe` first; if red, repair its first
  `norm_num` diagnostic, otherwise inspect `LaneBFrozenCapRowCap1409` before
  the remaining six. Do not run the full-row-cap set before the probe verdict.
