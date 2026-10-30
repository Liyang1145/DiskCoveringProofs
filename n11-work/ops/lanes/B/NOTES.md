EXPERT (2026-10-30):
- All seven `LaneBFrozenCapRowCap*` targets are CI-red; the first errors are vector indexing left as `![...] 2`, not a numerical cap failure.
- `norm_num [y_..., rowA]` does not unfold enough; use `simp only [y_..., rowA]` then `norm_num`, and remove no-goal trailing tactics. Do not invest another cycle here unless a bridge appears.
- The row caps still do not force `f0Lo`/`g`, so they cannot pay `RemainingTerminalRadius`; exact Fractions and byte audits are diagnostics, not proof.
- Highest leverage is the supervisor-only root import switch at `N11Formalization.lean:1961`: B12Main -> B13Main, then fresh root CI.
- No new B Lean lemma is required for that switch; `remaining_of_b13` already transfers the residual.
- Keep B13 at 1997 paid / 389 residual conditional. Do not call it root-reachable before root CI, and do not add B14 or row-cap content meanwhile.
- The root OOM in `SharedMomentConcreteSwitchBatch` is not a B13 mathematical verdict; SevenClassExclusions remains 0/7.

# Lane B notes

## 2026-10-30 - sessions 39-40 (condensed): row-cap failure diagnosis

- Run `41065332260` at `ede0d1c8` was job-green but all seven row-cap targets
  exited `1`. Its retained build log shows `hleft` goals containing
  `-![...] 2`; one-pass `norm_num [y_<node>, rowA, db, dbmVal]` therefore did
  not reduce negated vector applications. The former `rw`-then-`norm_num`
  endings also produced `No goals to be solved` when the rewrite closed a cap.
- Exact `Fraction` checks remained 7/7 nodes and 700/700 pairs with zero
  violations. These were proof-script failures, not arithmetic failures.
  `f0Lo`/`g`, 389 radii, SevenClassExclusions, and arbitrary-center remain
  unpaid.

## 2026-10-30 - session part 41: `Pi.neg_apply` row-cap repair, CI pending

- Inspected the retained CI build log for `41065332260` rather than inferring
  from the summary. The failing `hleft` goals reduce to sums such as
  `-![0, 0, 0, 1/4, ...] 2 + ... = -(3/8)`: `norm_num` had normalized the
  row difference into a negated function vector but still needed pointwise
  neg evaluation.
- Updated `n11-work/ops/lanes/B/split_rowcap_modules.py` so every one of the
  100 leaves per module has `hleft = <exact Fraction value>` proved by
  `norm_num [y_<node>, rowA, Pi.neg_apply]`, `hright = <exact Fraction value>`
  proved by `norm_num [db, dbmVal]`, then only `rw [hleft, hright]`. There is
  no unconditional trailing tactic. Regenerated
  `LaneBFrozenCapRowCap{1409,2337,2341,2356,2360,2368,2370}.lean`; frozen
  matrices and statements are unchanged.
- `split_rowcap_modules.py --check` exits `0`: 7/7 nodes, 700/700 ordered
  pairs, every weight sum `1`, zero violations, 100 leaves/module. Scope is
  exact rational arithmetic and generated-text equality, not Lean elaboration.
  `py_compile`, `git diff --check`, and the forbidden-token scan are clean.
- Emitter SHA256 `386B6FF2A133A50FA2737CF129F99696A050659D6049E14463BDC9981755155C`.
  Report SHA256 `C851EFCA0834334C98CF97173CFA859070CCA1ACA8989DBF90C0789BB1B896D9`.
  Module SHA256: 1409 `E4A66930C1FCD7739CFDEEA9D2915DF8BCAEE84ACA4586A2D59921401CB61AA2`;
  2337 `B497300CFAEB6DB3C27F9489964CC7555B68FF8C816BE65316FB9B64A383CB45`;
  2341 `D6249FB417A2210A4B07F6DB9C048759B3DAEF32F2A21F56CAAC6423EADA6A39`;
  2356 `A94A1930D74B4F66DA936883DD3CEA46AFB89C2C51977CB6BF2236801436C253`;
  2360 `D22F2B7305EE7A34F495AEB8C5D1B7EB4347288521BB405A0B395605BA401E65`;
  2368 `B35041A030B579D65D32E8A1EEFEA5A9F294A9B09B9D926ED30406BEBBCD3BFF`;
  2370 `B72120A5FEF7A59B747624274DB543F1DED6AD3C5B166F05A01CBE7CA32D7DA2`.
- A bounded 120 s local Mathlib probe timed out (`124`) under competing lane
  load; no local Lean verdict is claimed. `project_status.py --check` exits
  `0`, which is index consistency only.
- CI is pending for these exact hashes; none of the seven modules is paid.
  Still unpaid: seven row-cap kernel proofs, the `f0Lo`/`g` bridge, all 389
  residual radii, SevenClassExclusions, and the arbitrary-center theorem.
- Very next step: read fresh CI exits for these exact seven target hashes. If
  red, inspect that leaf's actual residual goal (especially `hright`); do not
  restore the one-pass or unconditional final `norm_num` ending.

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

## 2026-10-30 - sessions 31-33 (condensed): pair-leaf repair

- Runs `41037794295` and `41050208198` saw the earlier row-wide split and were
  red for all seven row-cap modules. Exact Python arithmetic was always 700/700,
  so these were proof-script failures, not cap violations.
- Reworked the generator to 100 independent explicit pair leaves per module,
  then to one-entry `hval : dbmVal i j = n` kernel `decide` leaves. No local
  Lean build or kernel result is claimed.

## 2026-10-30 - session part 37 (condensed): audit only; no Lean probe

- Reconfirmed 7 modules, 700/700 ordered pairs, weight sums 1, and zero cap
  violations; static checks were clean but all seven remained CI pending.
