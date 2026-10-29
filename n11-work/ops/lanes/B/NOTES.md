# Lane B notes

## 2026-10-29 - session part 16: explicit `Function.onFun` unfold in 56 dispatches

### Done
- Re-read the current guidance, Lane B entry, part-15 notes and `ci/LATEST.md`;
  `python tools/project_status.py --check` passed (index check only).
- Retrieved completed workflow run `40949277719` at `f30e46f0` and its full
  job log (workflow conclusion `success`; per-target exits Next1182 `1`,
  Next505Bounds `0`, B13 `1`, B13Main `1`). This run is **stale to the local
  `change` fix**: it predates that uncommitted source change.
- Exact stale failure: all 56 off-diagonal branches still expected
  `Function.onFun Disjoint part i j`; Lean's synthetic error recovery made
  `new_count` depend on `sorryAx`, confirming those declarations are not
  paid. B13/B13Main were import-blocked by Next1182 and received no independent
  verdict.
- Changed every off-diagonal branch in the emitter and generated module from
  `simpa [part]` to `simpa [part, Function.onFun]`, retaining the preceding
  `change Disjoint (part i) (part j)`. Updated the audit's exact-count check.

### Files (SHA256, uppercase)
- Next1182 `C3BD2A1254EE460D29E63A488CB7B37578DB19ECD78246FCDC7E5747CF831A22`
  (41,833 bytes).
- Emitter `8248CC972485566B2C71EC3695E6AEB60F6F65DF1A2AA6A3837E78CAAB420B24`.
- Emitter report `620D634AC202B663078F304D821069A3F0C09E8B5CF807D2F5FDC517FECA48E8`.
- Audit `C35D0A7C800163EEB3C97C585347D81312B84ABA435F22D7873A5E848E4C68B8`.
- Audit report `EEB3BB299428D01909DA6A27EDD2CEB25811D5B730F94B3FB73118134B7D7C24`.

### Checks executed (scope)
- Regenerated module and report (exit 0): 1182 ids, parts `168x7+6`, 57 literal
  blocks (max 21 cases), 28 interval-disjoint theorems, 8 diagonal + 56
  off-diagonal branches, 0 whole-set kernel decodes.
- `audit_next1182_blocks.py`, `audit_target_imports.py`, `py_compile`,
  `git diff --check`, and forbidden-token scan exited 0. Target import closure
  is 1919 modules with no missing/forbidden target. Scope is source/manifest
  inventory only, **not Lean elaboration**.
- A small `/workspace/tools/mathlib-probe` replay of the `PairwiseDisjoint`
  pattern hit its 180-second cap with no verdict; it is not evidence.

### Still unproved / unverified
- Next1182 `C3BD2A12...` is **CI pending / unpaid**; B13 and B13Main remain
  CI pending/unpaid pending a run that reaches them. Residual 389,
  `SevenClassExclusions`, and the arbitrary-center full-disk theorem remain
  unpaid.

### Next concrete step
- On the first CI run containing `C3BD2A12...`, require Next1182 exit `0` before
  interpreting B13. If Next1182 still fails, inspect its first full error block;
  do not treat synthetic `sorryAx` from an earlier error as a new source sorry.

## 2026-10-29 - session part 15: fix the 64 folded `onFun` dispatches

### Done
- Re-read `GUIDANCE.md`, Lane B entry, part-14 notes, `ci/LATEST.md`, and ran
  `python tools/project_status.py --check` (passed; index only).
- Pulled the full job log and artifact for n11 run `40949277719`, head
  `f30e46f0ae29a0b11304bddae3e4457ab8d3ba68`. That run supersedes the stale
  `LATEST.md` summary. Per-target exits were: Next1182 `1`, Next505Bounds `0`,
  B13 `1`, B13Main `1`; it is not a green Lean run overall.
- Exact Next1182 diagnosis from the full log: all 64 off-diagonal
  `simpa [part] using disjoint_s...` branches expected
  `Function.onFun Disjoint part i j`, while the supplied theorem simplified to
  `Disjoint S_i.newIDs S_j.newIDs`. The interval proofs and lower-bound
  transfers were not implicated.
- Added `change Disjoint (part i) (part j)` immediately after the
  `PairwiseDisjoint` intro, before `fin_cases`, and taught the emitter/audit
  this required line. Regenerated the module and reports.
- B13 and B13Main exited `1` in the same run, but no B13 source error was
  reached; treat them as import-blocked by Next1182, not independently tested.

### Files (SHA256, uppercase)
- Next1182 `F5D918A5799684216FD74EBF754B9BE37BEF622750F00A8167543BCBAF99BAEE`
  (40,937 bytes).
- Emitter `F4665D9F826D4D63F3AA1423378889D74FA1B0619AB38727A970D5F7A6DAD3D5`.
- Audit `EA9781393B4D3AD328E5F4A51F62E3BF360D95BF29277870827BCB8C7B602274`.
- Emitter report `E0851D3E9495A36319334C2E361DDBDA1E84AA8143D08E5AEBA99540B8F70613`.
- Audit report `EFFC52DE791EAC71C55DD43C490D971A0541F5A70702F159DEE1EFC2A2862E8C`.
- TARGETS unchanged: Next1182, Next505Bounds, B13, B13Main.

### Checks executed (scope)
- Emitter and `audit_next1182_blocks.py`: exit 0. Inventory is 1182 ids,
  parts `168x7+6`, 57 literal blocks (max 21 cases), 28 interval-disjoint
  theorems, 8 diagonal + 56 off-diagonal branches, one `change` exposure,
  8 lower-bound transfers, 0 whole-set kernel decodes. Scope is source,
  manifest and proof-shape inventory, **not Lean elaboration**.
- `py_compile`, `git diff --check`, and forbidden-token scan: exit 0.
- A narrowed Mathlib probe of `PairwiseDisjoint -> change Disjoint (part i)
  (part j)` was launched, but its import/elaboration did not finish inside the
  session cap. No Lean verdict from it.

### Still unproved / unverified
- Next1182 `F5D918A5...` is **CI pending / unpaid**. B13 and B13Main remain
  **CI pending / unpaid** because their target commands could not reach their
  own sources. Next505Bounds is CI green at `f30e46f0` only (kernel check).
- Residual 389, `SevenClassExclusions`, and the arbitrary-center full-disk
  theorem remain unpaid. A package or inventory success is not mathematics.

### Next concrete step
- On the next n11 CI artifact, require Next1182 exit `0` first. Then require
  separate B13 and B13Main exits `0`; if all three are green, issue the
  existing ROOT-IMPORT REQUEST for `EnergyTerminalBatchB13Main` and quote that
  run id. If Next1182 still fails, use its first full error block (not
  `errors_head`) and fix that exact tactic.

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
