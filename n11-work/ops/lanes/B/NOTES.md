EXPERT (2026-10-30):
- All seven `LaneBFrozenCapRowCap*` targets are CI-red; the first errors are vector indexing left as `![...] 2`, not a numerical cap failure.
- `norm_num [y_..., rowA]` does not unfold enough; use `simp only [y_..., rowA]` then `norm_num`, and remove no-goal trailing tactics. Do not invest another cycle here unless a bridge appears.
- The row caps still do not force `f0Lo`/`g`, so they cannot pay `RemainingTerminalRadius`; exact Fractions and byte audits are diagnostics, not proof.
- Highest leverage is the supervisor-only root import switch at `N11Formalization.lean:1961`: B12Main -> B13Main, then fresh root CI.
- No new B Lean lemma is required for that switch; `remaining_of_b13` already transfers the residual.
- Keep B13 at 1997 paid / 389 residual conditional. Do not call it root-reachable before root CI, and do not add B14 or row-cap content meanwhile.
- The root OOM in `SharedMomentConcreteSwitchBatch` is not a B13 mathematical verdict; SevenClassExclusions remains 0/7.

# Lane B notes
## 2026-10-30 - session 46: row-cap leaf proof repair, CI pending

- CI run `41082175973` remains red for all seven
  `LaneBFrozenCapRowCap*` targets. The recorded failures are unsolved goals and
  one heartbeat timeout, now attributable to the leaf script rather than the
  exact cap arithmetic. The same run is green for Next1182/B13/B13Main and for
  the newer refinement modules, but those are not row-cap payment.
- Changed `split_rowcap_modules.py` leaf bodies from
  `simp only [y_<node>, rowA, db, dbmVal, Pi.neg_apply] <;> norm_num` to
  `norm_num [y_<node>, rowA, db, dbmVal]`, then regenerated all seven
  `N11Formalization/LaneBFrozenCapRowCap{1409,2337,2341,2356,2360,2368,2370}.lean`.
  Frozen vectors/matrices/statements and the 100-leaf/10-row structure are unchanged.
- Removed the unhelpful, now-stale `LaneBFrozenCapRowCap1409Decide` target and
  generated file from `TARGETS.txt`; the current seven targets are the intended
  CI batch.
- Checks: emitter `--check` exit 0 with 7/7 matrices, 700/700 ordered pairs,
  weight sums all 1, zero exact-rational violations; `py_compile` exit 0;
  `git diff --check` exit 0. Emitter SHA256
  `E75DBAF22D694D06406FC6FDEE0EDBEAB38B1BA78ACB3C5BA17503939B81A1E8`;
  report `2661B0E63CF2B84CB3A18578D1847F322DD20E47121C3BECEC26F2BF52E39D46`.
  Module SHA256: 1409 `41B667E8...F2EB83`; 2337 `5B64C0F3...0CC34973`;
  2341 `4387B181...8D7D0F9A`; 2356 `38C519FD...C0E7376`;
  2360 `04404AB7...2E3F43`; 2368 `6067F76D...2546C6D`;
  2370 `D0458CBE...DA9D287`.
- Local Lean probes were not authoritative: `/workspace/tools/mathlib-probe`
  has no built granular Mathlib oleans and `lake env lean` stalled until the
  120 s bound; a monolithic 100-case `norm_num` probe reached its 180 s bound.
  Thus no local elaboration/kernel result is claimed.
- CI is **pending** for these seven bytes; none of the seven caps is paid. The
  `f0Lo`/`g` bridge, all 389 residual radii, SevenClassExclusions, and the
  arbitrary-center full-disk theorem remain unproved.
- Next concrete step: read the next CI's first row-cap diagnostic. If
  `norm_num [definitions]` still fails, emit one single-pair standalone probe
  from the first failing leaf and reduce only that leaf's proof to an explicit
  exact-fraction inequality; do not alter the frozen statement.

## 2026-10-30 - session 45: stricter B13Main root-switch parity audit

- Added `audit_b13main_signature_parity.py`; it compares both root-facing
  theorem blocks in B12Main/B13Main and permits only the batch/namespace rename,
  the B13 energy premise, and the explicit `remaining_of_b13` transfer.
- Exit 0, 5/5 checks: identical full-disk quantifier, identical
  `N11MainStatement SourceExactRoot.sourceRadius`, two theorems per module, and
  no change beyond that permitted energy substitution. B12Main SHA256
  `ED46AD0539E34924E202F60443314138BE2713C2247234D127C7F67EC94220C8`;
  B13Main `521CA436A8745EF197F76FCADEDCE2CF232B3B3643B977B997153E463FA41837`.
  Script `C270775A337A1C66B9F34E310E75B8CBC84BC62E8C8325A1B3D3D65D7D413972`;
  report `85EFBDE9947F080A8858042B8CF8860C4499E7AA5C77808B4D9AE01CEE6785B8`.
- Fresh `audit_b13_root_handoff.py` exit 0: root is `pre_handoff`, one old
  B12Main import, switch ready. `audit_b13_closure.py` exit 0: B11 310, B12
  815, B13 1997, Next1182 1182, sharp 120, terminals 2506, residual 389.
  Scope is static source/import parity plus inventories, not Lean elaboration,
  root CI, or mathematical payment.
- Row-cap probes remain unanswered/irrelevant to the residual: current
  `simp only ... <;> norm_num` bytes and `LaneBFrozenCapRowCap1409Decide` are
  CI pending. `f0Lo`/`g`, all 389 radii, SevenClassExclusions, and the
  arbitrary-center theorem remain unproved.
- Next concrete step: supervisor replaces only root line 1961 with
  `import N11Formalization.EnergyTerminalBatchB13Main`, reruns the handoff audit
  expecting `post_handoff`, and starts fresh root CI. Do not edit root here.


## 2026-10-30 - session part 27: residual 389 crosswalk

- Added `audit_residual389_crosswalk.py`, which parses the four literal chunks
  in `EnergyTerminalResidualCensusBase.lean`, the lane-C `residual389-census.json`,
  and the B13 closure report. It writes a 389-entry per-ID crosswalk and rejects
  any count, ordering, hash, match, or local-record drift.
- Result: exact 1:1 coverage, `389/389` matched, no unmatched IDs on either
  side. Both sides and the independent B13 closure digest equal
  `747447E233634FBC9D9321824148165AC866105FE0367AED27F6F8D9A2E07F46`.
  Chunk sizes are `100,100,100,89`; all chunks are sorted contiguous slices.
- Lane C exposes seven local survey records for these IDs, all with
  `pass_recorded=false` and `excluded_for_any_row_count=true`; the other 382
  have no local survey record. This crosswalk does not turn those exclusions
  into proof of `RemainingTerminalRadius`.
- Exact SHA256: script
  `642C31A1B200931EB02D1BB5AC98BC27EF34449BC2C55EF8EC7E245A5B9F59D1`;
  report `59FFCD5FF0DD4FFE67DC27255C7B775A481DBD8DFE07365A95311C49836D1E79`.
- Checks: `py_compile` exit 0; script exit 0 with 13/13 checks;
  `git diff --check` exit 0. Scope is source-ID inventory only, not Lean
  elaboration and not mathematical payment. No Lean target changed.
- Still unpaid: all 389 residual radius cases, SevenClassExclusions, and the
  arbitrary-center full-disk theorem. Root import remains supervisor-only.
- Next concrete step: for the seven locally represented exclusions, inspect
  whether lane C's exact row-cap certificates instantiate
  `PaidCellCertificateM` generically; if so emit one bounded Lean witness module
  for those seven IDs. Otherwise document the first missing certificate field.

## 2026-10-30 - session part 26 (condensed): static audit rerun

- Six lane-B source audits exited 0; closure remained B11 310, B12 815,
  B13 1997, Next1182 1182, sharp 120, terminals 2506, residual 389. This was
  static evidence only, not elaboration or payment.

## Current handoff (2026-10-30 09:48 UTC)

- **ROOT-IMPORT REQUEST:** after supervisor review, import only
  `N11Formalization.EnergyTerminalBatchB13Main` instead of
  `EnergyTerminalBatchB12Main` in the root.
- CI job `123993863813` on merged head `22719e0d` reports five exact green
  module exits, in order: Next1182 `0`, Next505Bounds `0`, DescentBounds `0`,
  B13 `0`, B13Main `0`. This pays B13's 1997-terminal module credit.
- Energy is still conditional: 389 terminal IDs remain in
  `B13.RemainingTerminalRadius`. SevenClassExclusions and the arbitrary-center
  full-disk theorem remain unpaid. Root integration is not yet changed.
- The run was still `in_progress` on later targets/root when read; do not turn
  the module exits into a completed-run or root verdict.

## 2026-10-30 09:54 UTC - session part 25: migration-safe root audit

- Upgraded `audit_b13_root_handoff.py` to accept exactly one valid root phase:
  pre-handoff (one old B12Main import) or post-handoff (one new B13Main
  import). Mixed and duplicate imports are rejected; B13Main import set,
  required names, target order, and forbidden-token checks are unchanged.
- Exact new-byte hashes: script
  `985E7C921AA199CE2914A837A627E13C3CE4686BFBA8BE1585DCB93ED7D1E8C7`;
  regenerated pre-handoff report
  `B0CCD386502D44A069C3D6B47BB909C1997641DF6F538E7FBF0BDD64C152CAB5`.
- Checks: `py_compile` exits 0; live pre root exits 0 (`pre_handoff`, ready);
  a temporary replacement root exits 0 (`post_handoff`, ready); mixed
  old+new root exits 1; duplicate new-import root exits 1. `git diff --check`
  exits 0. Scope is static source/import inspection only, not Lean
  elaboration, root CI, or proof credit.
- No new Lean module or target was added. The five module exits recorded above
  remain kernel evidence. B13 still has the explicit 389-ID residual premise;
  SevenClassExclusions and the arbitrary-center full-disk theorem are unpaid.
- Next: supervisor replaces only the B12Main import with B13Main, runs the
  audit again expecting `root_import_phase=post_handoff` and exit 0, then fresh
  CI must kernel-check the root. If supervisor has not acted, do not edit root.

## 2026-10-30 - session part 24: exact root-handoff audit

- Added `audit_b13_root_handoff.py`, a static check that binds the proposed
  replacement to B13Main hash
  `521CA436A8745EF197F76FCADEDCE2CF232B3B3643B977B997153E463FA41837`.
  It checks the sole old import, absence of the new import, exact three-import
  wrapper, required declarations, forbidden-token absence, and B13Main target
  ordering after B13. All seven checks pass; report
  `audit_b13_root_handoff-report.json` records the root is still pre-handoff.
- Exact new-byte hashes: audit script
  `F00761B3DA0C81445E57181B4BD2315742575AF8289F7E231C68FC0AE1631827`;
  report `80C7F66FB0893D175FEC398F6AF37564E8D290AE25D7C9610FCB55F8C16DF0DE`.
- Checks: audit exits 0; `py_compile` exits 0; `git diff --check` exits 0.
  Scope is static source/import inspection only, not Lean elaboration or root
  CI. Job `123993863813` was still `in_progress` when re-queried.
- No new Lean target was added because this session added no Lean module. The
  earlier five module exits remain the only kernel evidence; the 389 residual,
  SevenClassExclusions, and arbitrary-center full-disk theorem remain unpaid.
- Next: supervisor applies exactly the audited B13Main import replacement and
  commits these bytes; fresh CI must then kernel-check the root. Lane-B
  mathematical work remains the lane-C 389-ID residual linkage.

## Condensed history

- Next1182 (1182 ids, 57 literal blocks, 8 parts) and Next505Bounds are CI
  green. Closure is B11 310 + Next505 505 + Next1182 1182 = 1997 paid;
  2506 terminals, 120 sharp, residual 389.
- DescentBounds was repaired by split image/union layers and a corrected 27-id
  B09 high classification. Each `high_not_next_s01..s08` checks only one
  Next1182 part; the top theorem dispatches eight alternatives.
- Early failures were nonexistent `Finset.all_eq_true.mp`, large kernel
  decodes, broad `simp`/`whnf`, and a monolithic high exclusion. Repairs use
  `mem_image` + `fin_cases` + `norm_num [nodeID]`, with no enlarged heartbeats.
- B13Main originally compiled an optional lane-C census whose source was red.
  The core wrapper now has only C450Main, B13, and ActualMetricClassReduction.
- Shared frozen-dependency OOMs and root OOM are not lane-B mathematical
  verdicts. Source/inventory/byte audits are not Lean proof credit.

## Retained engineering facts

- `Finset.card_biUnion` takes disjointness explicitly. Pairwise disjointness of
  `Function.onFun` parts needs `change Disjoint (part i) (part j)` first.
- Part-local Next1182 lower bounds transfer globally through the conjunctive
  bound plus `omega`. `Finset.disjoint_left.mp` may need `(a := a)`.
- Emitters: `emit_next1182_top.py`, `emit_next505_bounds.py`,
  `emit_residual_census.py`, `emit_b13_descent_bounds.py`.
- Audits: `audit_next1182_blocks.py`, `audit_b13_descent.py`,
  `audit_b13main.py`, `audit_b13_closure.py`, `audit_target_imports.py`.
- Workflow's trailing `true` makes the top-level Build step non-semantic; only
  module `=== EXIT ... 0` lines and `summary.json` are verdicts.

## 2026-10-30 - sessions 22-23 (condensed): B13Main green on merged bytes

- Removed B13Main's optional lane-C census import; its hash became
  `521CA436A8745EF197F76FCADEDCE2CF232B3B3643B977B997153E463FA41837`.
- Job `123993863813` on head `22719e0d` gave exact kernel exits `0` for
  Next1182, Next505Bounds, DescentBounds, B13, B13Main. Scope is those five
  module targets only; the job was still `in_progress` on root.
- Closure audit: B11 310, B12 815, B13 1997, sharp 120, terminals 2506,
  residual 389. `project_status.py --check` exit 0 checks index declarations,
  not mathematics. Root still imports B12Main; replacement is supervisor-only.
- Full evidence: `ci-b13-green-20261030.json` and the static audit reports.

## 2026-10-30 - sessions 28-29 (condensed): frozen-cap API gap

- The seven public residual IDs (`1409, 2337, 2341, 2356, 2360, 2368, 2370`)
  have conditional exclusion trees only. Their packets do not force the fixed
  `f0Lo`/`g` equalities, so these wrappers do not pay a residual radius.
- `audit_frozen_cap_api_gap.py` / report SHA256 are
  `12A58F9D...15CFCF` / `A64D2E7B...C1FE9E`; 7/7 source checks pass.
- Part 29 created seven lane-B monolith row-cap candidates. CI at `34b14918`
  still showed the old frozen monoliths red: unsolved `norm_num` goals on six
  and a heartbeat timeout on 2356.

## 2026-10-30 - session part 30: split frozen-cap row proofs

- Exact-rational audit of all seven matrices: `700/700` ordered row caps pass,
  every weight vector sums to 1, and there are zero violations. Scope is
  arithmetic only, not Lean elaboration or payment.
- Rewrote the seven `LaneBFrozenCapRowCap<id>.lean` candidates so each
  monolithic 100-case proof is ten bounded row declarations plus a `fin_cases`
  dispatcher. Frozen matrices/statements are unchanged.
- Added idempotent exact-rational emitter/checker
  `ops/lanes/B/split_rowcap_modules.py` and report
  `split_rowcap_modules-report.json`. Lowercase SHA256: emitter
  `ef69d39e07360e8096588ac9762b15331d5295d88c97acc099a9b25da0f238bb`;
  report `3a5a9052fb1f7cd8288e1c7a4230983350fe17f3b40e7729c196069063770413`.
- Candidate module SHA256: 1409 `3d5dc70c62cb050dd783de7714d750b8588dbd42f337fcee89a737f8056940d7`;
  2337 `f01af4ee7ae948fca43f7037d6faef3b02a1c4a9d91a1e787f33297b84793e4f`;
  2341 `ad49e73219430f1eba8c197a22dae289c104cca76eebd17bc06c58c731946e37`;
  2356 `5725ab3aa017ee5dca6888dc719c2f8262ddad0f2f155730b4dcf36d03eddefc`;
  2360 `e5a88d48bcec5a21b6247e2fedf3d9c250755ef966adf13b4a865c03b069e084`;
  2368 `94f27b97e39f1364b999f24df8c03af33f1a57e4d7f306c7973a8069f6c79df0`;
  2370 `1b504d26e853126d3896fe968367e5109fcf8e23b826a55dc4975dfae6dae5ff`.
- Checks: `py_compile` exit 0; emitter `--check` exit 0; `git diff --check`
  exit 0. A bounded target-import audit hit the 30 s timeout (exit 124), so
  import closure is not claimed on these bytes. No local full-project Lean
  build was run.
- CI is **pending** for the split targets; none of the seven modules is paid.
  Still unpaid: all row-cap kernel proofs, the frozen-field bridge, all 389
  residual radii, SevenClassExclusions, and the arbitrary-center theorem.
- Next concrete step: read the first CI exit for the seven split modules. If
  any row still fails, isolate its exact `norm_num` diagnostic into ten
  single-pair leaves; do not build wrappers until all seven are green.

## 2026-10-30 - sessions 31-37 (condensed): pair-leaf repair history

- Earlier row-wide and `hval` pair-leaf layouts were CI-red for proof-script
  reasons. Exact arithmetic stayed 700/700; no Lean payment was claimed.
