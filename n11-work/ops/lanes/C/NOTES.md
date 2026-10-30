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

## Condensed history through part 106

- Core/M/MCap are CI-green; exact residual census is 389 ids, but only seven
  public HOST records exist and 382 are absent from the checked public/restored
  JSON and repository payloads.  Duplicate row-cap wrappers are retired.
- `FrozenCapPublicExcludedTree` is dependency-clean on the seven small row-cap
  modules and remains **CI pending**; its `hf0`/`hg` packet identifications and
  any bridge to `RemainingTerminalRadius` are still unpaid.
- Run `41021956701` was cancelled before producing a Lean exit.  Run
  `41023888165` (head `83710e22`) was in progress at this session's close.

## 2026-10-30 - part 107 (archive refinement discovery + restoration)

Did: audited `origin/ci/n11-build` archive
`ci-n11/drafts/energy/N11Formalization/EnergyRefineN*.lean` against the exact
389-ID census.  Found **57 distinct residual IDs** represented by refinement
drafts (14.65% of the residual set): `{3,23,37,38,39,40,2337,2341,2965,3040,
3112,3116,3149,3431,3432,3440,3490,3496,3517,3520,3522,3550,3564,3569,3573,
3578,3589,3623,3633,3738,3777,3778,3781,3783,3792,3794,3795,3800,3802,3803,
3807,3808,3810,3821,3825,3841,3851,3853,3854,3863,3865,3979,4162,4244,4313,
4650,4684}`; IDs SHA256 `cce8dda2bf536edf11b842966d1cf1e9cc75154b2e4f7b69ba814f4657d34057`.
All 57 have matching filename/terminal/`newIDs`/`node_radius`/axiom-print ids.
They total 6,949,370 bytes and 724 `decide +kernel` sites.  All 57 carry the
archive marker "pre-validated; NOT compiled"; 15 set `maxHeartbeats 0`, so the
family is not admissible as-is (the other 42 still need bounded kernel audit).

Restored two exact archive bytes as new current-tree modules: the 9,986-byte
generic `Paid16MatrixCellCertificate` framework and the 28,383-byte smallest
admissible-format candidate `EnergyRefineN2341` (six kernel checks, no forbidden
token).  Added both, framework first, to lane C CI targets.  This makes the next
kernel result decisive without claiming any packet or residual as paid.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/Paid16MatrixCellCertificate.lean`
  `a9c8cf1bf6a730809c023ca76f5566ebe6ca4d2a1afe0c1d47d248598a25eae1`.
- `n11-work/lean/N11Formalization/EnergyRefineN2341.lean`
  `49a253b6429af4a68c6915678ca00ee4c3a0d7b1ce76664924d22c08a887f23f`.
- `n11-work/ops/lanes/C/audit_archive_energy_refinements.py`
  `f865b8a260eebaef71f11833274e1495cae0fd1c7ad0550017cb72238086c074`.
- `n11-work/ops/lanes/C/archive-energy-refinement-audit.json`
  `394c23cc22a29e07ed6bd392dd23c05f87d4603a05781276d8277e99c8338d10`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `06b4bbd8f442215bc8edc6f109dfb13dc7f7d46afc50736344806df2d4e8bfff`.

Checks (exact scope): archive audit exits 0; 57/57 static theorem shapes match;
57/57 ids are in the 389 census; restored framework bytes exactly equal the
archive blob hash; framework imports the present `Paid16CellCertificate`; hard-
rule token scan of both restored modules is clean; new script passes
`py_compile`; `git diff --check` exits 0.  No Lean build was run locally, so the
framework and node 2341 are **CI pending**, not green, and pay no residual id.

Still unproved/missing: CI exit 0 plus axiom report for
`Paid16MatrixCellCertificate` and `EnergyRefineN2341`; `EnergyRefineN2341`'s six
kernel decisions and its generated data are unverified; 56 other archive drafts
need admissibility repair and kernel checks; the other 332 residual ids still
have no recovered certificate/data; seven exclusions still need `hf0`/`hg` and
a `RemainingTerminalRadius` bridge; B13/B13Main remain red.

Next: on the next CI run, require framework exit 0 first.  If green, read
`EnergyRefineN2341` exit and axiom output exactly; if red, fix only the first
compilation error (do not weaken the statement or add resource blowups).  If
both green, restore the remaining smallest bundle incrementally, never as one
aggregate.

## 2026-10-30 - part 108 (bounded local compile preflight)

Did: inspected the restored framework and node 2341 declarations/imports and ran
one bounded direct invocation, `timeout 25s lake env lean
N11Formalization/Paid16MatrixCellCertificate.lean` from `n11-work/lean`.  Lake
stopped during Mathlib revision checkout (`0df444a...`) because untracked files
would be overwritten.  It never reached Lean import resolution or parsing, so
this is neither a Lean error nor a pass.  No file in the project was modified by
that check; `git status --short` still shows only the part-107 lane files.

Conclusion/scope: local project compilation remains unavailable/unsafe under
the 2-core sandbox.  CI ordering in `TARGETS.txt` is correct: generic framework
immediately before node 2341.  Both remain **CI pending** and pay no residual
ID.  The unresolved mathematical obligations are unchanged (six node-2341
kernel decisions and packet validity; 56 other drafts; 332 missing
certificate/data IDs; geometry/remaining-radius linkage).

Next: supervisor commit/push part-107 bytes, then read CI's first Lean error for
`Paid16MatrixCellCertificate` only.  Do not run another local project build.

## 2026-10-30 - part 109 (restoration order audit)

Did: checked the current worktree and CI index.  The two part-107 modules are
still untracked, and `TARGETS.txt` orders the framework before node 2341.  The
latest indexed runs are `41017279843` (in progress) and `41011262474` (success,
older head); neither reports either new module, so both remain **CI pending**.
Sorted the 57 archive modules by byte size after excluding any with
`maxHeartbeats 0` or another forbidden-token hit.  Forty-two have clean static
token scans.  The first three restoration candidates are `2341` (28,383 B),
`2337` (28,421 B), and `3040` (28,437 B), each with six kernel `decide` sites.
The first two are already among the seven public exclusions; `3040` is the
smallest archive node that supplies previously absent payload material.

Checks (exact scope): `git status --short`, `TARGETS.txt` contents, the
part-107 static audit JSON, and a sort/filter over its 57 `modules` records.
No Lean build, CI log, kernel result, or mathematical payment was produced.

Next: when CI reports, inspect framework exit first and node 2341 second.  If
both are green, restore only `EnergyRefineN3040` (exact archive bytes), add it
after node 2341 in `TARGETS.txt`, and request a fresh CI run.  If either current
target is red, fix only its first compilation error.

## 2026-10-30 - part 110 (N2341 exact tree-data audit)

Did: added an independent exact-integer audit of the restored 3-node refinement
`EnergyRefineN2341`.  It recomputed the root scale identity against frozen
`DBMSourceTreeData` and both `DBMTreeKernel.Valid` split inequalities.  Result:
all 100 root entries satisfy `node0.db = 256 * source2341.db`; all 200 child
inequalities hold; root metadata is `terminal=false, i=1, j=6, m=589824,
left=1, right=2`; both children are terminal.  Therefore the tree/split layer
is exact; any failure in the Lean node is isolated to the framework or MPacket.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/audit_energy_refine_n2341_tree.py`
  `a050ba28a26b0b11e3104ea9e4346406ae75b4219d4ee8636a8dda222b95e2fe`.
- `n11-work/ops/lanes/C/energy-refine-n2341-tree-audit.json`
  `d4a1021cdc968b7d09ef22802e165958365d44ba59f701d2e6d5e48b6851814b`.

Checks (exact scope): audit exits 0; `py_compile` exits 0; `git diff --check`
exits 0.  GitHub run `41027178023` at commit `34b14918` was still in its Build
step when checked, so `Paid16MatrixCellCertificate` and `EnergyRefineN2341`
remain **CI pending**.  This audit is not a Lean/kernel verdict and pays no
residual ID.

Still unproved/missing: CI exit 0 and axiom report for the framework and node
2341; the six MPacket `decide +kernel` fields in node 2341; 56 other draft
modules; 332 absent certificate/data IDs; seven exclusion-to-radius bridges.

Next: read run `41027178023`'s artifact summary.  Require framework exit 0
before diagnosing node 2341; if red, fix only the first compile error.  If both
green, restore `EnergyRefineN3040` as the next disjoint payload bundle.
