# Lane C notes

## Standing constraints

- Kernel credit requires CI exit 0 and a mathematical consumer; an exact
  rational audit is diagnostic only.
- Keep green `FrozenCapRationalCore`, `PaidCellCertificateM`, and
  `PaidCellCertificateMCap` unchanged.  Wrappers remain conditional on packet
  `hf0`/`hg`; seven public residual IDs have exclusion payloads, while 382
  HOST records are absent.
- `FrozenCapWideFieldWitnesses` is CI-green.  `FrozenCapWideFieldRowCaps` is
  CI-red from 200000-heartbeat timeouts.  The conditional `ExcludedTree` is not
  a link to `RemainingTerminalRadius`, and duplicate row caps pay no credit.
- Do not replace exact roots/quantifiers with cached verdicts or decimals.

## Condensed history through part 96

- Core `40861839784`, M `40893868710`, and MCap `40949277719` are CI-green with
  clean axiom reports.  Exact census: 389 B13 residual IDs; seven public HOST
  payloads, 382 missing.
- Four/five-field positive-cap searches were superseded by wide-support
  exclusion witnesses.  Exact rational checks cover seven probability vectors,
  700 ordered row caps, and seven strict `gain < T^2` margins.
- Run `40988698121` made the old wide modules red.  Parts 82-89 replaced huge
  `norm_num` gains with core-theorem reuse; current witness SHA256 is
  `90a5c86e94d99e77bce33775939f8b67cee05f12f2c2530b96093147c81b7cc6`.
- Run `41001693009` / commit `e5875cf8` again shows Witnesses exit 0 but
  RowCaps exit 1: seven declarations time out at 200000 heartbeats.  Splitting
  100 pairs into 700 leaves (parts 90/93/96) did not yield a CI-green result.
- Part 91 established that the seven public residuals are genuine exclusions,
  not rescue candidates.  Part 92 scanned 702 public/restored JSON files
  (51,466,284 bytes; plus both oversized C450 files) and found zero payloads for
  the other 382 IDs.  This is not proof of external HOST absence.
- A bounded probe of the proposed precomputed-row tactic also exceeded 90 s;
  no local project build is authoritative.

## 2026-10-30 - part 97 (formal census consumer)

Did: added `FrozenCapResidualMembership.lean`, which proves the seven public
exclusion IDs `{1409,2337,2341,2356,2360,2368,2370}` are members of
`EnergyTerminalBatchB13.residualIDs` and are not in `paidIDs`.  The proof uses
the existing 389-element census equality and seven bounded
`decide +kernel` checks, each over the 100-literal `chunk0`; it does not use or
target the red RowCaps module.  This is a formal blocker record, not energy or
metric-class payment.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/FrozenCapResidualMembership.lean`
  `6ca0351e87976d1e1fc0b6e19a6dcac983883a5b8be6d0d7dc8b0a29f2e498ac`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `2ef0808436c1ffa6e686082673f065b0508bf7a8e3cac95342b8fd1b25c9cb71`.

Checks: all lane Python files pass `py_compile`; hard-rule scan of the new
module is clean; `git diff --check` exits 0.  The new Lean module is
**CI pending**; no local project build was run.

Still unproved/missing: CI exit 0 for the new module; a positive
`PaidCellCertificateM.Valid` packet or unconditional no-feasible-cell theorem;
382 HOST payloads; linkage of any exclusion to `RemainingTerminalRadius`.  The
seven public IDs are formally residual and unpaid, not paid.

Next: request targeted CI for `FrozenCapResidualMembership`.  If green, preserve
it as the formal blocker record and stop the duplicate row-cap family.  Continue
only if a HOST payload or a genuine geometric no-feasible-cell bridge appears;
otherwise report lane C blocked on the 382 absent records.

ROOT-IMPORT REQUEST: none; this module is a census consumer, not a root theorem.

## 2026-10-30 - parts 98-100 (census consumer, condensed)

Traced and audited `FrozenCapResidualMembership` (SHA
`6ca0351e...498ac`): its closure is 603 modules with zero missing imports and
exact seven ids, but B13 is red on missing `B11.paidIDs` /
`Paid16GeneralNext1182.newIDs/new_mem`.  Static audit exit 0 is not kernel
credit.  Correct activation order is DescentBounds -> B13 -> B13Main -> consumer.

## 2026-10-30 - part 101 (dependency-clean seven-node exclusions)

Did: added `FrozenCapPublicExcludedTree.lean`, a fresh seven-node exclusion
module that replaces the red bulk `FrozenCapWideFieldRowCaps` dependency with
the seven small green per-node row-cap modules and
`FrozenCapRowCapTreeBridges`.  It proves `excluded_<id>_tree : False` for
`{1409,2337,2341,2356,2360,2368,2370}` from a `PaidCellCertificateM.Valid`
packet pinned to that node plus the still-explicit `hf0`/`hg` packet
identifications.  This is a formal exclusion record, not a paid residual id or
a link to `RemainingTerminalRadius`.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/FrozenCapPublicExcludedTree.lean`
  `e5ca5e2a1968d1d50538c0f6917284e9a101931fb44caf1a6f11e4679d9673a3`.
- `n11-work/ops/lanes/C/audit_public_excluded_tree.py`
  `b18a5d0720c8a0c8506664ec69ad050fed567fa40b2be262e9cacfbe2d7d2515`.
- `n11-work/ops/lanes/C/public-excluded-tree-audit.json`
  `e4df1a7d5accb8c0fd138135b62b61a322ba267c27ea7ba9f17d71328de9b06b`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `4b9dd015b5a8a39374975f2ffa12791d25aed2bec9453d100009c85babd2b791`.

Checks (exact scope): static audit exit 0, 460 local modules in the target's
import closure, zero missing imports, all seven individual row-cap modules plus
bridges/witnesses/MCap present, and neither `FrozenCapWideFieldRowCaps` nor
`EnergyTerminalBatchB13` reachable.  Seven theorem ids are exactly the public
seven; hard-rule token scan clean; all lane Python files pass `py_compile`;
`git diff --check` exits 0.  The new module is **CI pending**; no local Lean
build was run, so this static audit is not kernel credit.

Still unproved/missing: CI exit 0 for the new module; the conditional `hf0`/`hg`
identifications are not supplied; no exclusion-to-`RemainingTerminalRadius`
bridge; B13/B13Main remain red, so `FrozenCapResidualMembership` remains
dependency-blocked; 382 HOST payloads remain absent.

Next: kernel-check `FrozenCapPublicExcludedTree` alone in targeted CI.  If green,
use it as the seven-node exclusion record and do not target the bulk-row-cap
wrappers again.  Then wait for Lane B's B13 repair before rechecking
`FrozenCapResidualMembership`; do not edit B13 from lane C.

ROOT-IMPORT REQUEST: none; conditional exclusions do not pay the root theorem.

## 2026-10-30 - part 102 (consume CI / re-audit pending target)

Did: consumed `ops/ci/LATEST.md` and re-ran the static audit on the unchanged
part-101 bytes.  Latest *completed* run `41011262474` (`9f499ca6`) predates the
new target: its exits still list `FrozenCapWideFieldRowCaps=1`,
`EnergyTerminalBatchB13=1`, `EnergyTerminalBatchB13Main=1`, and its root build
later OOM-killed at `SharedMomentConcreteSwitchBatch`; neither
`FrozenCapPublicExcludedTree` nor `FrozenCapResidualMembership` appears in that
run.  Run `41017279843` was still in progress, so the new module remains
**CI pending**, not green.

Audit result (exact scope): `audit_public_excluded_tree.py` exit 0; target SHA
unchanged at `e5ca5e2a1968d1d50538c0f6917284e9a101931fb44caf1a6f11e4679d9673a3`;
closure 460 modules, zero missing local imports, all seven per-node row caps
plus bridges/witnesses/MCap present, forbidden bulk/B13 dependencies absent,
and all seven theorem ids exact.  No Lean build was run locally.

Still unproved/missing: targeted CI exit 0 for
`FrozenCapPublicExcludedTree`; `hf0`/`hg` packet identifications; any
exclusion-to-`RemainingTerminalRadius` bridge; green B13/B13Main for
`FrozenCapResidualMembership`; 382 HOST payloads.  No kernel or energy credit.

Next: after the supervisor commits/merges this worktree, require CI exit 0 for
the unchanged `FrozenCapPublicExcludedTree` target before using it as the
seven-node exclusion record.  Do not target the bulk row-cap wrapper.  Then
recheck `FrozenCapResidualMembership` only when Lane B's B13 is green.

## 2026-10-30 - part 103 (withhold dependency-red consumer target)

Did: removed `FrozenCapResidualMembership` from CI `TARGETS.txt` because its
B13 dependency remains red and it cannot produce kernel credit on this tree.
Kept its source and static prerequisite audit intact; added an explicit
comment recording the activation condition.  Condensed stale parts 98-100.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/TARGETS.txt`
  `fc90fea6f082e848f5f6e4ba4f80ffc76b0a03aeeea719a76452d0a5c511c74e`.
- `n11-work/lean/N11Formalization/FrozenCapPublicExcludedTree.lean` unchanged,
  `e5ca5e2a1968d1d50538c0f6917284e9a101931fb44caf1a6f11e4679d9673a3`.

Checks (exact scope): parsed target list now has five Lean targets, ending in
`FrozenCapPublicExcludedTree`; `audit_public_excluded_tree.py` exit 0 with 460
modules, zero missing imports, forbidden bulk/B13 absent, and exact seven ids;
all lane Python passes `py_compile`; `git diff --check` exit 0.  No Lean build
was run locally.  The new tree remains **CI pending**, not green.

Still unproved/missing: targeted CI exit 0 for the tree; explicit `hf0`/`hg`
packet identifications; exclusion-to-`RemainingTerminalRadius` bridge; B13 green
then consumer exit 0; 382 HOST payloads.  No energy/class credit.

Next: after supervisor commit, inspect CI for
`FrozenCapPublicExcludedTree` and its axiom report.  Keep the membership consumer
withheld until Lane B reports B13/B13Main CI-green on recorded hashes.

## 2026-10-30 - part 104 (CI scope check)

Did: queried GitHub Actions run `41017279843` directly; it is completed with
conclusion `success` at `2026-10-30T07:41:06Z`, head
`0361ae51f9a877ee782fc8e43c7f08e758f18f7f`.  That head's lane C target list
still ends in `FrozenCapWideFieldRowCaps` and contains no
`FrozenCapPublicExcludedTree.lean`, so the success covers only the older tree.
Re-ran `audit_public_excluded_tree.py` against unchanged target bytes: exit 0,
460-module closure, zero missing imports/forbidden deps, exact seven ids.

Files/SHA256 (lowercase): target
`e5ca5e2a1968d1d50538c0f6917284e9a101931fb44caf1a6f11e4679d9673a3`;
`TARGETS.txt` `fc90fea6f082e848f5f6e4ba4f80ffc76b0a03aeeea719a76452d0a5c511c74e`.

Checks scope: remote run metadata plus static source/import audit only.  No local
Lean build.  `FrozenCapPublicExcludedTree` remains **CI pending**, not green.

Still missing: CI exit 0 and axiom report for the unchanged tree target; explicit
`hf0`/`hg` identifications; exclusion-to-`RemainingTerminalRadius` bridge; green
B13/B13Main; 382 HOST payloads.  No kernel, energy or class credit.

Next: supervisor must commit this worktree, then CI must run on the new head and
build `FrozenCapPublicExcludedTree`; inspect that new run's exit code and
`#print axioms` output before calling the seven-node tree green.

## 2026-10-30 - part 105 (post-merge CI dispatch)

Did: checked the newly merged lane-C head through the GitHub API.  Head
`430f8902ad4a466e4f4d9b1d37b2f993047719ec` has three workflow runs:
`n11-lean-build` run `41021956701` is still **pending**; the scoped
`math-checks.yml` run `41021956775` succeeded, while `delivery-bytes.yml` run
`41021956901` failed.  The math replay success is a fresh-arithmetic check, not
a Lean build and not kernel credit for lane C.  No source bytes changed in this
part.

Current hashes: `FrozenCapPublicExcludedTree.lean`
`e5ca5e2a1968d1d50538c0f6917284e9a101931fb44caf1a6f11e4679d9673a3`;
`TARGETS.txt` `fc90fea6f082e848f5f6e4ba4f80ffc76b0a03aeeea719a76452d0a5c511c74e`.

Checks (exact scope): remote workflow metadata only; no local Lean build and no
CI Lean exit yet.  `FrozenCapPublicExcludedTree` remains **CI pending**, not
green.

Still missing: `n11-lean-build` exit 0 and axiom output for the tree; explicit
`hf0`/`hg` packet identifications; exclusion-to-`RemainingTerminalRadius`
bridge; green B13/B13Main; 382 HOST payloads.  No kernel, energy or class
credit.

Next: poll run `41021956701` after it starts; compile its per-target exits for
exactly `FrozenCapPublicExcludedTree`, inspect the corresponding log's axiom
report, and only then record CI green/red.

## 2026-10-30 - part 106 (runner queue check, exact audit)

Did: re-queried workflow run `41021956701` at head
`430f8902ad4a466e4f4d9b1d37b2f993047719ec`: it remains `pending`, and its jobs
endpoint is empty, so it has not acquired a runner.  Re-ran the static tree
audit: exit 0, 460-module closure, zero missing imports, no forbidden
bulk/B13 dependencies, exact seven ids.  `git diff --check` exits 0.

Hashes (lowercase): tree `e5ca5e2a...9673a3`; targets `fc90fea6...c74e`;
audit script `b18a5d07...2515`; audit JSON `e4df1a7d...b06b`.  Source bytes
unchanged from part 105.

Checks scope: remote run/jobs metadata and static import/source audit only; no
Lean build and no CI exit.  Tree remains **CI pending**, not green.

Still missing: workflow execution and per-target exit 0 with axiom report;
`hf0`/`hg` identifications; exclusion-to-`RemainingTerminalRadius` bridge;
green B13/B13Main; 382 HOST payloads.  No kernel, energy or class credit.

Next: when the job starts, read the `FrozenCapPublicExcludedTree` target exit
and axiom output; if green, record it, otherwise diagnose the first Lean error.
