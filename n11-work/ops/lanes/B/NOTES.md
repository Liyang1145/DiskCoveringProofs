## 2026-10-31 - session 96: Fourteen green; Sixteen recursion repaired

- Downloaded run `41201323694` on `3551ab87`, artifact `13044243893`
  (`64791EDA...79BA63`), summary `E9F7745E...F33344`. The masked-success run
  proves `RefineFourteen` and `FourteenMain` exit `0` (kernel green), while
  `RefineSixteen` and `SixteenMain` exit `1`.
- First owning diagnostic: `EnergyTerminalBatchB13RefineSixteen.lean:31:2`,
  `maximum recursion depth has been reached`, from `tauto` over the four
  unfolded paid-set unions. The later checks and axiom reports in this module
  are not proof credit for the failed declaration.
- Replaced `tauto` with an explicit bounded five-case decomposition:
  Fourteen -> Thirteen -> Twelve -> Eleven, then dispatch base / Eleven-new /
  0037 / 3112 / 3116. No recursion-limit raise, `decide` enlargement, or new
  target. New Sixteen SHA256 `094F9C9B3917180EF1BD19654B984E93C2F5DBC32AF4613F212F796BA52D003A`
  (old `E7C0CBD8...097C5`). Fourteen stays `0BCDA687...0AB4F`;
  `TARGETS.txt` stays `EB52F2B4...16DD01`.
- Added `ci-verdict-41201323694.json`. Checks after the repair:
  `audit_b13_refine_sixteen.py` and `audit_b13_refine_fourteen.py` exit `0`
  with `ok:true`; `git diff --check` exits `0`. These are static
  source/inventory and arithmetic checks only, not Lean elaboration.
- Conditional arithmetic remains 2013 paid / 373 residual, but is **not paid**:
  fresh exit-0 artifacts for Sixteen and SixteenMain are still required.
- Still unproved: 373 residual radii; `f0Lo`/`g` bridge; SevenClassExclusions
  (`0/7`); arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits the exact Sixteen bytes and evidence,
  then serial CI must show both Sixteen modules exit `0` with clean
  `#print axioms`. If green, request the supervisor-only root switch from
  B13Main to SixteenMain, preserving explicit SevenClassExclusions.

## Earlier session 95 (condensed)

- Closed Fourteen `paid_count` (`2010 + 1 = 2011`) and Sixteen `new_count`
  (`1 + 1 = 2`) plus `paid_count` (`2011 + 2 = 2013`) by exact count rewrites
  and `omega`, without enlarging generated decisions. Evidence:
  `ci-repair-20261031-fourteen-sixteen.json`.


## 2026-10-31 - session 94: fresh CI isolates and repairs Fourteen arithmetic

- Downloaded completed run `41195990232` (`cc16dff4`) artifact `13043056783`
  (`47F36EF9...BFE066`). The workflow says success, but `summary.json` says
  Thirteen/ThirteenMain exit `0`; Fourteen, FourteenMain, Sixteen, and
  SixteenMain exit `1`. Exact evidence: `ci-verdict-41195990232.json`.
- First owning diagnostic (Fourteen import blocks Sixteen): at
  `EnergyTerminalBatchB13RefineFourteen.lean:66:2`, after both alias/count
  rewrites the goal is `2010 + #EnergyRefineN3116.newIDs = 2011`, while
  `EnergyTerminalBatchB13Refine3116.new_count` only proves the cardinality
  `= 1`. This is an open arithmetic normalization, not a failed disjointness.
- Appended `norm_num` to Fourteen `paid_count`; static audit now requires that
  exact closing line. New Fourteen SHA256
  `722F42C6195325676EB5C8545D0C911A9F87FF40DC39F09A39E0139E03BD9FB3`
  (pre-repair `36C34D...D33E`). Audit SHA256 `D79666A9...A68C5`; new
  Fourteen report `7867E7F3...D705A`; Sixteen report `ED27F0FB...48FF1`.
- Checks: Fourteen audit exit `0`, Sixteen audit exit `0` (both static
  source/inventory only), `py_compile`, forbidden-token scan, and
  `git diff --check` exit `0`. `audit_target_imports.py` hit `timeout 60`
  without output, so no closure-count check this part. No local Lean verdict.
- Still unproved: fresh exit-0 artifacts for all four Fourteen/Sixteen targets;
  373 conditional residual radii; `f0Lo`/`g` bridge; SevenClassExclusions
  (`0/7`); arbitrary-center full-disk theorem. Do not record `2013/373` yet.
- Next: supervisor commits these bytes, then serial CI. If Fourteen is green,
  read Sixteen's first diagnostic next; only four exit-0 artifacts permit the
  `2013/373` handoff and consideration of the SixteenMain root switch.

## Earlier 2026-10-31 sessions 91--93 (condensed)

- Run `41193732877` artifact was old-byte evidence: direct row caps green, lane-B
  duplicate wrappers red. They were replaced by thin aliases of the direct
  modules' `row_cap`; details/hashes remain in
  `split_rowcap_modules-report-session91.json` and
  `ci-verdict-41193732877.json`.
- Session 92 repaired Fourteen alias unfolding; the fresh run in session 94
  proved that repair still left the `2010 + 1 = 2011` arithmetic step open.

## 2026-10-31 - session 88 (parts 1-3): Fourteen alias-count repair; CI pending

- Repaired `EnergyTerminalBatchB13RefineFourteen.lean::paid_count`: after
  rewriting the disjoint-union card and Thirteen's count, close with
  `simpa [newIDs] using EnergyTerminalBatchB13Refine3116.new_count`, avoiding
  the failed direct rewrite. Audit guards now require the actual Thirteen base
  and the alias count.
- Current Fourteen sha `9D1B9D6A706C011CCBF85CA855F66827C4C9707DA6CEAC7CA78DBBFBD84301C7`;
  Fourteen audit `222608F6...B8B3BB4BA`; report `EE0A9CA2...F922F`;
  `TARGETS.txt` `EB52F2B4...E16DD01`. Static audits pass; fresh CI is pending.

# Lane B notes

## 2026-10-31 - session 91 diagnosis of sessions 69--85 (condensed)

- Earlier runs established 700/700 exact arithmetic but red leaves kept moving
  through definitional `change`, vector lookup, dispatch, and symbolic
  `norm_num`. Session 85 returned to the direct `FrozenCapRowCap*` shape, yet
  run `41193732877` still showed all eight lane-B duplicates red while all seven
  direct modules were green. Session 91 therefore removed the duplicate proofs.

## Row-cap history (condensed)

Session 84's full-`simp` attempt was superseded. Older runs established
700/700 exact arithmetic but failed at definitional `change`, vector lookup,
then dispatch/probe issues; these are engineering iterations, not proof credit.

## Session 81 and 79 (condensed)

CI `41176805557` first showed the vector-lookup residue but the attempted
`List.getElem_cons_*` repair was the wrong namespace. Session 79 had confirmed
700/700 exact arithmetic and weight sums with zero violations, but had no local
Lean verdict.

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

## Session 69 (condensed)

- Fresh CI isolated the Fourteen alias failure; later repairs supersede its
  intermediate tactic attempts. Preserve the final session-92 shape.

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
