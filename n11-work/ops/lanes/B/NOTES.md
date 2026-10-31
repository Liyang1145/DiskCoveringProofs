EXPERT (2026-10-31):
- The singleton/union refinement is mathematically sound and the only current real energy reducer.
- Serialize only Fourteen, FourteenMain, Sixteen, SixteenMain; require four exit-0 artifacts and clean `#print axioms`.
- Record 2013/373 only after `paid_count` and `remaining_of` are green; they price sixteen singleton refinements, not 373 radii.
- Then request the supervisor-only root switch from B13Main to SixteenMain, preserving the explicit SevenClassExclusions premise.
- If red, inspect the first owning diagnostic. Do not enlarge `decide +kernel`, `maxRecDepth`, or generated decision terms.

## 2026-10-31 - session 89 (part 4): revalidate Fourteen handoff; CI pending

- Re-read guidance/lane/CI and ran `project_status.py --check` (exit `0`, index
  scope only). Fourteen static audit is `ok:true`, 20/20 checks; `git diff
  --check` exits `0`. No Lean file changed in this part.
- Retried a minimal exact-pattern `Finset.card_union_of_disjoint` + alias
  `simpa` probe with cached Mathlib: `timeout 180 lake env lean` exits `124`
  during import, so there is no local elaboration verdict.
- Hashes unchanged: Fourteen `D638A5C4...21E7E1BB`, audit
  `222608F6...B8B3BB4BA`, report `EE0A9CA2...F922F`, targets
  `EB52F2B4...E16DD01`. Sixteen audit remains its prior static `ok:true`.
- Still unproved: fresh serial CI exits for Fourteen, FourteenMain, Sixteen,
  SixteenMain; 373 conditional residual radii; `f0Lo`/`g` bridge;
  SevenClassExclusions (`0/7`); arbitrary-center full-disk theorem.
- Next: supervisor commit/push the unchanged alias repair; inspect the real CI
  artifact in target order and repair only the first diagnostic if red.

## 2026-10-31 - session 88 (parts 1-3): Fourteen alias-count repair; CI pending

- Repaired `EnergyTerminalBatchB13RefineFourteen.lean::paid_count`: after
  rewriting the disjoint-union card and Thirteen's count, close with
  `simpa [newIDs] using EnergyTerminalBatchB13Refine3116.new_count`. This
  avoids the failed direct `new_count` rewrite exposed by alias unfolding.
- Added `paid_count_uses_alias_count` to
  `audit_b13_refine_fourteen.py`, requiring the alias-count proof and rejecting
  the old direct rewrite. Re-raised `paid_base_is_thirteen` to require the
  actual alias definition (`...Thirteen.paidIDs ∪ newIDs`).
- Checks (static only): Fourteen audit `ok:true`, 20/20 checks; Sixteen audit
  `ok:true`, 17/17; `py_compile`, `git diff --check`, and
  `project_status.py --check` exit `0`; forbidden-token scan empty. A minimal
  exact-pattern Mathlib probe timed out, so no local Lean verdict exists.
- Hashes: Fourteen `D638A5C4652B1C11915F23FBA8E1A2296D772F0F8D60EDBA7DF8C5B021E7E1BB`;
  Fourteen audit `222608F670BCE7240643AB5AEB6AC22FA5C9B63334FF6704CE9D322B8B3BB4BA`;
  report `EE0A9CA2DC862D81D82224B52B88B612E3B0EB67CEA33B14DB066703089F922F`;
  `TARGETS.txt` `EB52F2B496FAFDCCA8FFA0281C11751975C00A0BCF094A497A274753AE16DD01`.
  FourteenMain, Sixteen, and SixteenMain remain byte-unchanged.
- Still unproved: fresh serial CI exits for Fourteen, FourteenMain, Sixteen,
  and SixteenMain; 373 conditional residual radii; `f0Lo`/`g` bridge;
  SevenClassExclusions (`0/7`); arbitrary-center full-disk theorem.
- Next exact step: supervisor commit, then fresh serial CI in order Fourteen,
  FourteenMain, Sixteen, SixteenMain. If Fourteen is red, repair only its first
  diagnostic. Do not record `2013/373` or request the SixteenMain root switch
  until all four exits are `0`.

# Lane B notes

## 2026-10-31 - session 85: row caps restored to the CI-green frozen proof shape

- Read the completed public run `41182882564` (`7f7e6f3b`) summary/log. It
  kernel-checked the *older committed* lane bytes: probe and all seven caps
  exit `1`. Probe line 40 was `No goals to be solved`; cap dispatch red from
  line 546 because `simpa only [...]` left `Fin.succ`/`⟨n, _⟩` indices while the
  scalar leaves used numerals. This is a stale-byte diagnosis, not session 84's
  full-`simp` fix.
- Replaced the dispatch design in `split_rowcap_modules.py` with the shape
  already CI-green in `FrozenCapRowCap1409.lean`: each leaf states the actual
  `∑ q : Fin 9, y_node q * rowA i j q` and closes with
  `norm_num [y_node, rowA, db, dbmVal, Fin.sum_univ_succ]`; each row and the
  final theorem use `fin_cases` followed by `exact`. No `simpa`, `first`, or
  scalar-to-sum matching remains. Regenerated all seven lane cap modules.
- Updated `LaneBRowCapDecideProbe.lean` to three sum-form representative leaves
  for pairs `(0,1)`, `(4,5)`, `(9,9)`.
- Static checks (not kernel proof): exact emitter `--check` exit `0`;
  `py_compile`, `git diff --check`, `project_status.py --check` exit `0`;
  forbidden-token scan empty; seven nodes, 100 leaves and 100 `exact` dispatch
  branches per module, 700/700 exact rational caps, weight sums `1`, zero
  violations. Local Lean has no Mathlib oleans and was not used as evidence.
- Fresh report: `n11-work/ops/lanes/B/split_rowcap_modules-report-session85.json`.
  SHA256: emitter `381E3BADEAF5F9739E83F21E7EBB7FE49309D7B4EC1BF410BFD368BB7A85E24F`;
  probe `E1E61727A7912558E9B60FE725C726A075F2D3B54367934A0F610EC5AB57AF8A`;
  1409 `E231371BBBF162545A34AD0D152B8A46D72968E8C6D7E65989E96C5046D4234A`;
  2337 `2B6F96095655887D6865794E0000AC6E78D4F34D6710A38C6BCB085B0DD8B55D`;
  2341 `E4F8F65F0F9DDF46834F433BEA2819567365EDC92AE849D54EA8B1993080AD83`;
  2356 `7F89C5D38C225B35CB3AE33CB98F7DECEFA55463A97E94FFCEB515EDBE524D1B`;
  2360 `F513BF3B5202EA459D6E3F8A243E20CC96ADBF35FD499D9B2192E36CB2C022E0`;
  2368 `3F7F6FB11494765C672B85C84D0C9C751DFA9CEC1F3DA4A571FA348EE984DB33`;
  2370 `BC9AF51B2573B566A6AA494048CE88DAC2CC1FE0ECCCB995B6F2B9CF83D22528`.
  `TARGETS.txt` unchanged; no new module target.
- Still unproved: fresh kernel exits for these bytes, public excluded tree,
  Fourteen/Sixteen dependants, 373 conditional residual radii, `f0Lo`/`g`
  bridge, SevenClassExclusions (`0/7`), arbitrary-center full-disk theorem.
- Next concrete step: supervisor commits unchanged, then fresh serial CI must
  give probe exit `0`, followed by 1409 and the six other caps. A static pass or
  public-module precedent is not lane-B proof credit.

## 2026-10-31 - session 84 (condensed)

Live-log diagnosis above replaced session 84's unverified full-`simp` fix.
Session 84 static report remains at `split_rowcap_modules-report-session84.json`;
its emitter/probe/cap hashes are superseded and must not be quoted as current.

## Row-cap history (condensed)

Older runs established 700/700 exact arithmetic but failed first at definitional
`change`, then at unresolved `![...]` matrix lookups, then at the dispatch/probe
issues diagnosed above. These are engineering iterations, not proof credit.

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
