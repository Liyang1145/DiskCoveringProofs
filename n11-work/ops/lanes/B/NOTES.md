# Lane B notes

## Condensed history (parts 1-18, 2026-10-29)

- Next1182 top aggregate was written and repeatedly repaired: `simpa [part]`
  -> `change Disjoint (part i) (part j)` -> `simpa [part, Function.onFun]`.
  Current source `C3BD2A12...`, reproducible from `emit_next1182_top.py`
  (`8248CC97...`); audits exit 0. All of it is **CI pending / unpaid**.
- CI runs `40949277719`/`40802064355`/`40935785584` never reached a lane-B
  source error after the fix: failures were (a) the pre-fix `Function.onFun`
  mismatch, (b) OOM kills of shared frozen deps (`DBMSourceTreeData`,
  `Ladder49_jt_kkt_z`, `SharedMomentConcreteSwitchBatch` — the last is outside
  lane B and killed the root target in `40935785584`).
- Next505Bounds `FA5CA6EB...` and B13Next505Bounds are CI green; B13 and
  B13Main source exist and are import-blocked on Next1182.

## Retained engineering facts

### Next1182
- Top aggregate is `Finset.univ.biUnion part` over eight sub-aggregates.
  Membership uses `mem_biUnion` + `fin_cases`; cardinality uses
  `Finset.card_biUnion hdisj` and `Fin.sum_univ_succ`.
- The repaired lower-bound proof transfers every part-local lower bound to the
  global 2565 target with `have hb := (part_sNN_bounds n h).1` then `omega`.
  Never use a direct part exact for parts 2-8.
- `Set.PairwiseDisjoint` unfolds through `Function.onFun`; after `intro` use
  `change Disjoint (part i) (part j)` before `fin_cases`.
- 57 literal blocks of at most 21 ids keep every kernel decode at 21 literals.
- The prior trailing `norm_num` in `new_count` caused `No goals to be solved`.

### B13 / Next505
- `EnergyTerminalBatchB13Next505Bounds` replaces B13's 505-element kernel
  decode with 25 literal blocks (24x21 plus one id). Next505 module SHA256
  `FA5CA6EB9CD75158085EDDD3C0CB464AB7F96CF124FCE40C303EB176D31D46F2`;
  emitter `BFE4A4C422CDF5F54E60AD21E9C78AE96BDBBC7FD7717556B3FACFAE9203480A`.
- B13 descent: `b11_lt` uses B10 (100 ids) plus Remaining210 (210 ids);
  `next505_lt` uses the 25-block module. If B13 reports `b10_lt` or
  `remaining210_lt`, split those decodes hierarchically rather than raising
  limits.
- B13Main forwards residual 389 through B12's `remaining_of_b12`; the
  literal-census variant uses `EnergyTerminalResidualCensus.remaining_iff_b13`.
- **ROOT-IMPORT REQUEST (only after CI green):** import
  `EnergyTerminalBatchB13Main` instead of `EnergyTerminalBatchB12Main`.

### Working rules retained
- `Finset.card_biUnion` takes disjointness explicitly:
  `Finset.card_biUnion hdisj`.
- `Finset.disjoint_left.mp` needs `(a := a)` when the element is implicit.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`; audit: `audit_next1182_blocks.py`.
- A successful source/inventory audit is not proof. CI is the project-module
  Lean authority; local probes use `/workspace/tools/mathlib-probe`.
- Do not claim payment for Next1182, B13, or B13Main until CI is green.

## 2026-10-29 - session part 17 (same slot, part 5): determinism recheck of the `onFun` fix

### Done
- Re-read NOTES part 16; confirmed the local `Next1182` source is exactly the
  fixed `C3BD2A12...` (41,833 bytes), with 56 `simpa [part, Function.onFun]`
  off-diagonal branches and the single shared `change Disjoint (part i) (part j)`.
- Re-ran `emit_next1182_top.py` (exit 0): regenerated the module to the same
  SHA256 `C3BD2A12...`, so the fix is reproducible, not hand drift.
- Re-ran `audit_next1182_blocks.py` (exit 0): 1182 ids, parts `168x7+6`,
  57 literal blocks (max 21 cases), 28 interval-disjoint theorems, 8 diagonal +
  56 off-diagonal dispatches, 0 whole-set kernel decodes; report retains
  `top_sha256 C3BD2A12...`. Scope remains source/manifest inventory, **not**
  Lean elaboration.

### Files (SHA256, uppercase)
- `Paid16GeneralNext1182.lean` `C3BD2A1254EE460D29E63A488CB7B37578DB19ECD78246FCDC7E5747CF831A22`.
- `emit_next1182_top.py` `8248CC972485566B2C71EC3695E6AEB60F6F65DF1A2AA6A3837E78CAAB420B24`.
- `audit_next1182_blocks.py` `C35D0A7C800163EEB3C97C585347D81312B84ABA435F22D7873A5E848E4C68B8`.
- TARGETS unchanged: Next1182, Next505Bounds, B13, B13Main.

### Still unproved / unverified
- Next1182, B13, B13Main all remain **CI pending / unpaid**; only a CI run on
  this exact source can move them. Residual 389, `SevenClassExclusions`, and the
  arbitrary-center full-disk theorem remain unpaid.

### Next concrete step
- On the next CI run for this tree, read Next1182's verdict first. If it is
  green, inspect B13's first real error (not an import-block cascade); if red,
  quote the first full error block verbatim before changing anything.

## 2026-10-29 - session part 19: defeq-fallback for the 56 pairwise dispatches

### Done
- Read `GUIDANCE.md`, Lane B, condensed notes, `ci/LATEST.md` and ran
  `python tools/project_status.py --check` (exit 0; index check only).
- Confirmed the only lane-B Lean blocker left is `Paid16GeneralNext1182`;
  `EnergyTerminalBatchB13` (`paidIDs := B12.paidIDs ∪ Next1182.newIDs`,
  `paid_count 1997`) and `B13Main` are written and merely import-blocked on it.
- Hardened `new_count`'s `Set.PairwiseDisjoint` proof: every off-diagonal
  branch is now `first | (change Disjoint S_i.newIDs S_j.newIDs; exact
  disjoint_sIJ) | (simpa [part, Function.onFun] using disjoint_sIJ)`. The first
  branch is a pure defeq transport (independent of simp lemmas for
  `Function.onFun`/matrix cons), so a simp-set regression cannot red the module;
  the previous `simpa` syntax stays as fallback.
- Emitter change is in `emit_next1182_top.py`; regenerated module, updated
  `audit_next1182_blocks.py` assertions (56 fallback branches, `.symm` count 56).

### Files (SHA256, uppercase)
- `Paid16GeneralNext1182.lean` `5D941203EDF2222D28389F467BEC254D71F486CA26EC7F8414E629EA34FAA9B1`
  (49,701 bytes; supersedes `C3BD2A12...`).
- `emit_next1182_top.py` `5A670144F705FBD7C664A1C0BE2CE5BFFD02A53232EFDCB21472E3F5892EFE0E`.
- `audit_next1182_blocks.py` regenerated report `audit_next1182_blocks-report.json`
  (top_sha256 `5D941203...`).
- TARGETS unchanged: Next1182, Next505Bounds, B13, B13Main.

### Checks executed (scope)
- `emit_next1182_top.py` exit 0; `audit_next1182_blocks.py` exit 0: 1182 ids,
  parts `168x7+6`, bounds `2565..5007` non-overlapping, 57 literal blocks
  (max 21), 28 interval-disjoint theorems, 8 diagonal + 56 off-diagonal
  dispatches, 56 defeq-fallback branches, 0 whole-set kernel decodes.
  `py_compile` and `git diff --check` exit 0. Scope is source/manifest
  inventory, **not Lean elaboration**.
- Two `/workspace/tools/mathlib-probe` probes (`import Mathlib`; then
  `Mathlib.Data.Finset.Card`) both hit 95-170 s caps with no verdict on this
  weak FS; neither is evidence.

### Still unproved / unverified
- Next1182 `5D941203...` is **CI pending / unpaid**; B13, B13Main likewise.
  Residual 389, `SevenClassExclusions`, arbitrary-center full-disk: unpaid.
- Root `N11Formalization` also fails on non-lane-B OOM of
  `SharedMomentConcreteSwitchBatch` (run `40935785584`) — not a lane-B defect.

### Next concrete step
- On the first CI run containing `5D941203...`: require Next1182 exit `0`,
  then separate B13 exit `0`, then B13Main exit `0`; only then issue the
  root-import request (quote run id). If Next1182 is red, copy the first full
  error block and check whether `change Disjoint S_i S_j` was the failing step.

## 2026-10-30 - session: static recheck + audit (no CI change)

### Done
- Re-read GUIDANCE/Lanes/NOTES/ci LATEST; ran `python tools/project_status.py --check` (exit 0).
- Ran `audit_next1182_blocks.py` (exit 0): 1182 ids; parts 168x7+6; 57 literal blocks (max 21); 28 interval-disjoint theorems; 8 diagonal + 56 off-diagonal dispatches; 56 defeq-fallback branches; 0 whole-set decodes. top_sha256 `5D941203...` (49,701 bytes); emitter `5A670144...`.
- `py_compile` on emitter/audit (exit 0); `git diff --check` (exit 0).
- Reconfirmed B13 (`paid_count 1997`, residual 389) and B13Main source internally consistent; targets unchanged.
- CI LATEST still run `40935785584` on older tree (Next1182 red "Type mismatch" lines 582-590); no new run contains `5D941203...`.

### Still unproved / unverified
- Next1182 `5D941203...`, B13, B13Main: CI pending/unpaid. Residual 389, SevenClassExclusions, arbitrary-center full-disk: unpaid.
- Suspected Next1182 red site is `lower_bound` omega lifts (parts 2-8); emitter keeps 8 `have hb := (part_s...).1; omega` transfers (audit count 8).

### Next concrete step
- On first CI run containing `5D941203...`: require Next1182 exit 0, then B13 exit 0, then B13Main exit 0; then ROOT-IMPORT REQUEST for B13Main. If red, quote first full error block and check `change Disjoint` / `lower_bound` step.

## 2026-10-30 - session part 2: repaired source enters CI

### Done
- Re-read GUIDANCE, Lane B, NOTES and CI index; `project_status.py --check` exit 0.
- Confirmed HEAD `76b6835e5d6ff2c166cac703a0d55f33dc54303d` contains
  `Paid16GeneralNext1182.lean` SHA256 `5D941203...` (49,701 bytes) and emitter
  `5A670144...`. This is the defeq-fallback revision, not the older red source.
- GitHub Actions run `40973981403` (workflow `n11-lean-build`, head `76b6835e`)
  is the first run bound to this source. At observation its single `build` job
  was `in_progress` in step 7 (`Build`); no target verdict or error log exists yet.
  Run `40973981437` (math) succeeded and `40973981433` (delivery) failed; neither
  is the lane-B Lean kernel verdict.

### Checks executed (scope)
- API metadata only: run/head/status binding above; no local Lean build.

### Still unproved / unverified
- Next1182 `5D941203...`, B13, B13Main remain **CI pending / unpaid**. Residual
  389, `SevenClassExclusions`, arbitrary-center full-disk theorem remain unpaid.

### Next concrete step
- Poll run `40973981403` to completion and read the Build log. Require distinct
  exit-0 evidence for Next1182, then B13, then B13Main before a root-import request.

## 2026-10-30 - session part 3: live CI poll + red-site source audit

### Done
- Re-read GUIDANCE, Lane B, NOTES and CI index; `project_status.py --check` exit 0.
- Queried GitHub API run `40973981403` (repo `Liyang1145/DiskCoveringProofs`): head
  `76b6835e5d6ff2c166cac703a0d55f33dc54303d`; status `in_progress`, conclusion null;
  build job `123806191726` in step 7 `Build` (started 2026-10-30T00:05:10Z). No Lean
  target verdict yet; live log download is API `Not Found` while running.
- Confirmed local Next1182 remains SHA256 `5D941203...` (49,701 bytes), emitter
  `5A670144...`; no source drift.
- Traced the prior red site precisely: in `cea391a9`, lines 581-588 of
  `Paid16GeneralNext1182.lean` were `exact (part_sNN_bounds n h).1`. A conjunction
  projection does not match the required `2565 ≤ n.val` when the part lower endpoints
  differ by part; this explains all seven reported type mismatches (old lines 582-588).
  The current source instead extracts the full conjunctive bound as `hb` and closes
  each branch with `omega` (current source lines 579-596), so the fallback is exactly
  at the previous red site. This is source inspection, not elaboration.

### Still unproved / unverified
- Run `40973981403` has **no verdict yet**; Next1182 `5D941203...`, B13 and B13Main
  remain CI pending/unpaid. Residual 389, `SevenClassExclusions`, and arbitrary-center
  full-disk theorem remain unpaid.
- Prior `cea391a9` red is stale relative to current source and is not the current verdict.

### Next concrete step
- Poll `40973981403` to completion and read its Build log. Require exit 0 for
  Next1182 first, then B13, then B13Main; only then request root import of B13Main.
