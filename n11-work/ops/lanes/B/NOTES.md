# Lane B notes

## 2026-10-31 - session 68: handoff byte/hash recheck (CI still pending)

- Re-ran the six-target static gate in the current worktree. `audit_b13_refine_sixteen.py`
  exits 0 with all 16 checks true (`2013` paid, `373` residual), the Thirteen audit exits
  0, and `audit_target_imports.py` exits 0 with a 1965-module closure and no missing or
  forbidden imports. `git diff --check` exits 0. Scope is source/inventory arithmetic and
  import resolution only, not Lean elaboration or kernel proof credit.
- Reconfirmed the exact handoff hashes: Thirteen `F62B93EB...E9252E`, ThirteenMain
  `D46E758C...D2784375`, Fourteen `12D107B3...DD0E4`, FourteenMain `9478C19F...C3FE7`,
  Sixteen `055F8BA3...C28851`, SixteenMain `A3103831...8FECF`, TARGETS
  `69E4E5A5...9F612`, and CI verdict evidence `63B92837...74C407`.
- The latest indexed CI remains run `41123531381` on `cc04268c`; run `41141569628`
  was overall green but its artifact records exit `1` for all six handoff modules, with
  the redundant Thirteen tactic now repaired. No fresh post-repair artifact exists, so
  all six remain **CI pending** and none is proof credit.
- Still unproved: the conditional 373 residual radii, the `f0Lo`/`g` bridge,
  SevenClassExclusions (`0/7`), and the arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits these exact bytes unchanged; fresh serial CI
  must report exit `0` separately for all six targets before the root-import request is
  considered. Repair only the first failing declaration from its exact diagnostic.

## 2026-10-31 - session 67: post-repair static chain gate

- Re-ran the post-repair checks on the exact six modules CI must kernel-check:
  `EnergyTerminalBatchB13RefineThirteen`, `...ThirteenMain`, `...Fourteen`,
  `...FourteenMain`, `...Sixteen`, and `...SixteenMain`.
- Results: `audit_b13_refine_sixteen.py` exits 0 with all 16 checks true and
  arithmetic `1997 + 16 = 2013` paid / `389 - 16 = 373` residual;
  `audit_b13_refine_thirteen.py` exits 0 with no failures and confirms removal
  of the redundant Thirteen tactic; `audit_target_imports.py` exits 0 with
  closure 1965, no missing and no forbidden imports; `git diff --check` exits 0.
  Scope is static source/inventory/arithmetic and import resolution only, not
  Lean elaboration or kernel proof credit.
- Exact source hashes: Thirteen `F62B93EB...E9252E`, ThirteenMain
  `D46E758C...D2784375`, Fourteen `12D107B3...DD0E4`, FourteenMain
  `9478C19F...C3FE7`, Sixteen `055F8BA3...C28851`, SixteenMain
  `A3103831...8FECF`; TARGETS `69E4E5A5...9F612`.
- Still unproved: all 373 residual radii, the `f0Lo`/`g` bridge,
  SevenClassExclusions (`0/7`), and the arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits these exact bytes unchanged; fresh
  serial CI must record exit `0` separately for all six targets above before
  any proof credit or root-import switch is claimed.

## 2026-10-31 - session 66: chain-level regression audit

- Re-read session 65 and confirmed the repaired Thirteen close is
  `rw [... EnergyTerminalBatchB13RefineTwelve.new_count]` with no trailing
  tactic; the goal closes by reduction of `11 + 1 = 12`.
- Extended `audit_b13_refine_sixteen.py` to pin the repaired close against
  reintroduction of a redundant `norm_num`, and to check the complete stage
  arithmetic `Seven=2004, Eight=2005, Eleven=2008, Twelve=2009,
  Thirteen=2010, Fourteen=2011, Sixteen=2013` from the actual chain sources.
- Checks: `audit_b13_refine_sixteen.py` exits 0 with `ok:true`; its report was
  refreshed. Scope is static source/inventory arithmetic only, not Lean
  elaboration. The local Mathlib singleton-union probe timed out under the
  two-core limit, so no unverified Lean source rewrite was made.
- Still unproved: all 373 residual radii, the `f0Lo`/`g` bridge,
  SevenClassExclusions (`0/7`), and the arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits the repaired Thirteen, updated audit,
  and report unchanged; then fresh serial CI must record exit `0` for the six
  chain targets from `RefineThirteen` through `RefineSixteenMain`.

## 2026-10-31 - session 65: post-repair static revalidation

- Re-read session 64 and checked GitHub Actions before editing. The newest
  `n11/work` runs are still `41141569628/581/692` at `c63cb61e`; no run exists
  for the repaired working tree. The repair and evidence remain uncommitted in
  this worktree, so there is still no post-repair Lean proof credit.
- Verified the six chain source hashes: Thirteen `F62B93EB...E9252E`, ThirteenMain
  `D46E758C...D2784375`, Fourteen `12D107B3...DD0E4`, FourteenMain
  `9478C19F...C3FE7`, Sixteen `055F8BA3...C28851`, SixteenMain
  `A3103831...8FECF`. The repaired Thirteen removes only the redundant
  `norm_num`; the surrounding `rw` already closes `twelve_new_count`.
- Rechecked the count decomposition around the former failure. Despite its name,
  `EnergyTerminalBatchB13RefineTwelve.new_count` states the singleton
  `EnergyRefineN0037.newIDs.card = 1`; Thirteen combines that with
  `EnergyTerminalBatchB13RefineEleven.new_count = 11` to obtain 12. This is
  intentional but naming-sensitive and should not be "simplified" without a
  replacement total-count theorem.
- Checks run this session: all three
  `audit_b13_refine_{thirteen,fourteen,sixteen}.py` scripts exit 0 with
  `ok:true`; `audit_target_imports.py` exits 0 with a 1965-module closure and no
  missing/forbidden imports; `py_compile` and `git diff --check` exit 0. Scope is
  static source/inventory/arithmetic only, not Lean elaboration.
- Still unproved: all 373 residual radii, the `f0Lo`/`g` bridge,
  SevenClassExclusions (`0/7`), and the arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits the Sixteen chain and CI evidence
  unchanged, then a fresh serial run must report module exits `0` for all six
  targets. If green, request the supervisor-only root import switch; lane B does
  not edit the root.

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
