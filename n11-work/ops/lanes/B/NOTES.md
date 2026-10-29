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

## 2026-10-29 - session part 17: stale-run confirmation + local audit

### Done
- Re-read `GUIDANCE.md`, Lane B, part-16 notes and `ci/LATEST.md`.
- Queried GitHub API for run `40949277719`: workflow `completed success`, head
  `f30e46f0ae29a0b11304bddae3e4457ab8d3ba68`, updated `2026-10-29T21:02:39Z`.
  Its target failures still concern the pre-fix Next1182 bytes, so the workflow
  conclusion is not evidence for the local `C3BD2A12...` source.
- Re-ran `audit_next1182_blocks.py` (exit 0): 1182 ids; eight parts
  `168x7+6`; 57 literal blocks (max 21); 28 interval-disjoint theorems; 8
  diagonal + 56 off-diagonal dispatch cases; 8 lower-bound transfers; zero
  whole-set kernel decodes. Source SHA256 remains
  `C3BD2A1254EE460D29E63A488CB7B37578DB19ECD78246FCDC7E5747CF831A22`
  (41,833 bytes), matching part 16.
- Confirmed B13/B13Main source and prior closure/import audits remain internally
  consistent (B13 count 815+1182=1997; residual inventory 389). These are static
  checks only.

### Still unproved / unverified
- Next1182 `C3BD2A12...` remains **CI pending / unpaid**; B13 and B13Main remain
  **CI pending / unpaid** and were import-blocked on the tested hash. Residual
  389, `SevenClassExclusions`, and the arbitrary-center full-disk theorem are
  unpaid.

### Next concrete step
- Wait for a CI run whose Next1182 artifact/source hash is `C3BD2A12...`.
  Require Next1182 exit `0` first, then separate B13 and B13Main exits `0`.
  Only then issue the root-import request, quoting the run id.

## 2026-10-29 - session part 18: hash/audit recheck; CI access absent

### Done
- Re-read guidance, lane B, the part-17 notes, and `ci/LATEST.md`; the index
  status check passed (inventory scope only).
- Confirmed the working-tree Next1182 still has SHA256
  `C3BD2A1254EE460D29E63A488CB7B37578DB19ECD78246FCDC7E5747CF831A22`
  and emitter SHA256
  `8248CC972485566B2C71EC3695E6AEB60F6F65DF1A2AA6A3837E78CAAB420B24`.
- Re-ran `audit_next1182_blocks.py` (exit 0) and `git diff --check` (exit 0):
  1182 ids; parts `168x7+6`; 57 literal blocks (max 21); 28 interval
  disjointness theorems; 8 diagonal + 56 off-diagonal branches; 8 global
  lower-bound transfers; 0 whole-set kernel decodes.
- `gh` is unavailable in this worktree/session, so no post-fix run or artifact
  was accessible. `ci/LATEST.md` still records run `40949277719` against the
  stale pre-fix Next1182 bytes.

### Still unproved / unverified
- Next1182 `C3BD2A12...` is **CI pending / unpaid**. B13 and B13Main are
  **CI pending / unpaid**. Residual 389, `SevenClassExclusions`, and the
  arbitrary-center full-disk theorem remain unpaid.

### Next concrete step
- On the next CI artifact, first require Next1182 `C3BD2A12...` exit `0`.
  Then require separate B13 and B13Main exits `0`; only then request the root
  import and quote the successful run id.

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
