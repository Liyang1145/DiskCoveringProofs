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

## 2026-10-30 - parts 107-110 (archive restoration, condensed)

Audited `origin/ci/n11-build` and found 57 distinct residual refinement drafts
(6,949,370 B; 15 use forbidden `maxHeartbeats 0`).  Restored exact bytes for the
CI-green generic `Paid16MatrixCellCertificate` and `EnergyRefineN2341`, then the
currently pending `EnergyRefineN3040`.  Exact tree audits for 2341 and 3040 pass:
100 root scale entries, 200 split inequalities, root split `i=1,j=6`, terminal
children.  A bounded local preflight failed during Lake checkout and is not a
Lean verdict.  Full historical hashes remain in git history; current artifacts
are recorded below.
## 2026-10-30 - part 111 (N2341 green; N3040 restored and audited)

Did: read artifact `12966223963` from run `41027178023` (commit `34b14918`).
Its `summary.json` records exit 0 for both `Paid16MatrixCellCertificate` and
`EnergyRefineN2341`; the job conclusion is success and `built_count` is 5.
These two modules are therefore **CI green**, not merely draft or pending.

Restored exact archive bytes as `EnergyRefineN3040.lean` (git blob object
`99738366706c00b7032c58086736b9b37b6e8669`, matching
`origin/ci/n11-build:ci-n11/drafts/energy/N11Formalization/EnergyRefineN3040.lean`;
SHA256 `7fcd5e3b8d528dfd3602a1f84709ca66c54e78de198116caec28d8b47ac4e057`).
Added it to `TARGETS.txt` after N2341.  Independent exact-integer audit checks
all 100 root scale entries and all 200 split inequalities: zero mismatches,
root metadata `terminal=false, i=1, j=6, m=491520, left=1, right=2`, both
children terminal.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/audit_energy_refine_n3040_tree.py`
  `be05b3803b4e3854655a6d4c8c038233b9eec9d36756f6e5498b88666c440559`.
- `n11-work/ops/lanes/C/energy-refine-n3040-tree-audit.json`
  `11a75ec22e4b86be3a2952f5dfdfa1b6173156b73b6029144cb669ba1a5dd0a2`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `988bc2e0dd9419640d9160e3bb8ad66367fc9bac83e2457e4d35b3b35d3e6707`.

Checks (scope): blob hash equality, audit exit 0, `py_compile` exit 0,
`git diff --check` exit 0, forbidden-token scan clean.  `EnergyRefineN3040` is
**CI pending**; the six MPacket kernel checks remain unverified.  No local Lean
build was run.  It pays no residual ID until CI exits 0 and a consumer links it.

Still unproved/missing: CI for N3040; 55 other archive drafts; 332 absent
certificate/data IDs; seven exclusion-to-radius bridges.  Next: require N3040
exit 0.  If green, restore non-public payload `EnergyRefineN2965` (28,441 B)
with the same exact-byte and tree audit; if red, fix only its first error.

## 2026-10-30 - part 112 (N2965 restored and tree-audited)

Did: restored exact `origin/ci/n11-build` archive bytes as
`EnergyRefineN2965.lean` (git blob `22b863e9992ff2d3cf99192034a4dbb9b79357e9`,
SHA256 `fa6abd13bf6a12f0dc3b6fd90af620102c628bb307484866d20752844899306a`).
Generalized the exact-integer tree auditor to accept a node argument, preserving
the N3040 report and adding N2965.  N2965 passes all 100 root scale entries and
all 200 split inequalities; root metadata is `terminal=false, i=1, j=6,
m=458752, left=1, right=2`, and both children are terminal.  Added N2965 after
N3040 in CI targets.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/audit_energy_refine_n3040_tree.py`
  `16eec03c370489f10e68157247ea1532a8d2b78ec035584f21ee31a5865d3d1c`.
- `n11-work/ops/lanes/C/energy-refine-n2965-tree-audit.json`
  `89a268e968388edacac9b2e9b4ebdb086578ebce694fb1c9506a8fe1fae58786`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `4efdd6fab6e94d87e5ee00f7a91de573181e269a41ebd66138c7ee422bf645b8`.

Checks (exact scope): archive byte equality (`cmp` and git blob), both audit
invocations exit 0, `py_compile` exit 0, forbidden-token scan clean, and
`git diff --check` exit 0.  No Lean build or kernel check was run.  N3040 and
N2965 remain **CI pending**; neither pays a residual ID.  Their six MPacket
`decide +kernel` sites and axiom reports are unverified.  The tree audits prove
only the integer split/scale layer against frozen `DBMSourceTreeData`.
GitHub run `41035092539` (`n11-lean-build`, head `22719e0d`) was still
`in_progress` on job `123993863813` when checked; it includes N3040 but not the
uncommitted N2965 target.

Still unproved/missing: CI exits and axiom reports for N3040/N2965; 54 other
archive drafts; 332 absent certificate/data IDs; seven exclusion-to-radius
bridges; B13/B13Main red.  Next: require N3040 exit 0, then N2965.  If both are
green, restore non-public `EnergyRefineN2337` only after checking its exact
payload is not merely one of the seven already-public exclusions; if red, fix
only the first compilation error.

## 2026-10-30 - parts 113-114 (N3440/N3589/N3623 restored, condensed)

Restored exact `origin/ci/n11-build` blobs for three non-public refinements and
added them to `TARGETS.txt`. Each passed the exact-integer auditor: zero errors
among 100 root-scale entries and 200 split inequalities; root `(false,1,6,m,1,2)`
with both children terminal. SHA256: N3440 `6420041457438e3f3a9102f0995eabe64e99a48b74047c2d9391a0319a9e72b1`
(m=491520), N3589 `02992f0cbc721f3f4ca087b5b28f5430ae8853513ff00e39891759c4a6362e1b`
(m=491520), N3623 `7b3eca9d0c37c2889ccf4331f7ee69579be43ba9f1dd05696f2a5b5698f326ee`
(m=507904); audit JSONs `f68dea65...6697ca`, `e8ab1da7...f9159ba`,
`9246abf2...c6e9bc1` respectively. Additional checks: `py_compile`, forbidden
token scan, `git diff --check`, all exit 0. These modules are **CI pending**;
tree audits cover only DBM split/scale, and no residual is paid without green
CI plus a mathematical consumer.

## 2026-10-30 - part 115 (N3633 restored and tree-audited)

Restored exact archive blob `c5701aa84e6c59a8650d750d695cb023d697dbd3` from
`ci-n11/drafts/energy/N11Formalization/EnergyRefineN3633.lean` as
`EnergyRefineN3633.lean`; added `N11Formalization.EnergyRefineN3633` after
N3623 in CI targets. The exact-integer audit passes all 100 root scale entries
and all 200 split inequalities. Root metadata is `terminal=false, i=1, j=6,
m=507904, left=1, right=2`; both children are terminal.

Files / SHA256 (lowercase):
- `n11-work/lean/N11Formalization/EnergyRefineN3633.lean`
  `8192fc0e83d46d600c9380f7d84da35f2b254dd1914de76e5eec12127723c59e`.
- `n11-work/ops/lanes/C/energy-refine-n3633-tree-audit.json`
  `29120643c7a7baa912ed3a66f00f22788b2f135f5023cc014cd86afd1d5201db`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `6b93a18632296a23dece3fa594be1689b8490aa9cd1c6f78741e198ab4d16bd0`.

Checks (scope): archive blob equality, audit exit 0, `py_compile` exit 0,
forbidden-token scan clean, `git diff --check` exit 0. No Lean build or kernel
check was run. N3633 is **CI pending**; MPacket validation, axiom report, and
residual payment are unverified. The audit covers only DBM split/scale data.

Still unproved/missing: CI exits/axioms for N2965/N3040/N3440/N3589/N3623/N3633;
50 other archive drafts; 332 absent certificate/data IDs; seven
exclusion-to-radius bridges; B13/B13Main red. Next: require N3633 CI exit 0;
if green enumerate the remaining draft inventory and restore the next bounded
non-public refinement, if red fix only its first compilation error.
