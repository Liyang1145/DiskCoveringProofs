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

## 2026-10-30 - part 98 (census-consumer dependency audit)

Did: traced `FrozenCapResidualMembership` -> `EnergyTerminalResidualCensus`
-> four C01-C04 parts -> `EnergyTerminalResidualCensusBase` ->
`EnergyTerminalBatchB13`.  The new module has the correct B13 interface
(`mem_residualIDs_iff`, `residualIDs_eq`), but CI cannot green it while B13 is
red: run `41001693009` reports B13 exit 1 from
`EnergyTerminalBatchB13DescentBounds` unknown identifiers
`EnergyTerminalBatchB11.paidIDs` and `Paid16GeneralNext1182.newIDs/new_mem`.
Thus its CI status is dependency-blocked, not merely pending.  The seven
`decide +kernel` membership leaves are each over the 100-literal `chunk0`;
no project build was run.  A 90 s standalone Mathlib probe of the proof pattern
timed out with no output and is diagnostic only.

Still unproved/missing: B13/DescentBounds CI exit 0; then exit 0 for this module;
382 HOST payloads; any link from exclusion witnesses to
`RemainingTerminalRadius`; no energy/class credit.

Next: wait for Lane B's B13 repair, then rerun targeted CI for
`FrozenCapResidualMembership` without changing its proof.  If B13 still fails,
report the dependency on Lane B rather than editing B13 from lane C.

## 2026-10-30 - part 99 (repaired dependency + target hygiene)

Did: re-read GUIDANCE/LANES/NOTES/LATEST and reran `project_status.py --check`
(exit 0; handoff index only).  Confirmed lane B's missing-import repair is now
committed at `8c61ad4f`; the current tree carries DescentBounds
`5c2b2ed8...`, B13 `3dd37313...`, B13Main `2a6a206f...`.  Added
`audit_residual_membership_prereqs.py`, which statically resolves the consumer's
local import closure, requires B13/DescentBounds/B11/Next1182, checks the seven
literal ids, and scans the consumer for forbidden tokens.  Removed the known-red
duplicate `FrozenCapWideFieldRowCaps` target so CI does not spend another ~84 s
on a family already disproven as a route to the cap result; Witnesses and the
seven exclusion payloads remain untouched.

Files / SHA256 (lowercase):
- `n11-work/ops/lanes/C/audit_residual_membership_prereqs.py`
  `9340af619e62a4c4a9aaad715beea822324e7414a7cbfd17e88b341f83537c8f`.
- `n11-work/ops/lanes/C/residual-membership-prereq-audit.json`
  `fa382046080ff2b365bca5cb65c23675152f3105e8892ce9d054769a200edcaf`.
- `n11-work/ops/lanes/C/TARGETS.txt`
  `5c60fd15a12cfd32b2d565ff1ea61be231de00dc2a6ecfe55ff92edb97bd4a76`.

Checks (exact scope):
- prerequisite audit exit 0: five checks true, 603 local modules in the
  transitive closure, zero missing local imports, required B13 modules present,
  consumer ids exactly `{1409,2337,2341,2356,2360,2368,2370}`, no forbidden
  tokens in the consumer source.
- lane B `audit_b13_closure.py` exit 0: all 13 static inventory checks
  (B11 310, B12 815, B13 1997, Next1182 1182, residual 389, sharp 120).
- `py_compile` and `git diff --check` exit 0.  No Lean build was run locally.

Still unproved/missing: `FrozenCapResidualMembership` is **CI pending** on
current bytes; B13/B13Main likewise need a CI-green run on the repaired hashes.
No positive `PaidCellCertificateM.Valid` packet, no unconditional
no-feasible-cell theorem, 382 HOST payloads absent, and no exclusion-to-
`RemainingTerminalRadius` link.  Static closure success is not a kernel proof.

Next: after the supervisor commits this worktree, require CI exit 0 in order
DescentBounds -> B13 -> B13Main -> FrozenCapResidualMembership.  If the consumer
is green, preserve it as the formal blocker record and seek a genuine geometric
no-feasible-cell bridge or HOST payloads; do not reopen duplicate row caps.

## 2026-10-30 - part 100 (fresh static recheck)

Did: on the unchanged consumer bytes, reran
`audit_residual_membership_prereqs.py` and `project_status.py --check`.  The
prerequisite audit again exits 0: closure 603, zero missing local imports, all
five checks true, exact consumer ids
`{1409,2337,2341,2356,2360,2368,2370}`, no forbidden tokens.  Recomputed
SHA256 values match part 99:
- `FrozenCapResidualMembership.lean`
  `6ca0351e87976d1e1fc0b6e19a6dcac983883a5b8be6d0d7dc8b0a29f2e498ac`.
- `TARGETS.txt`
  `5c60fd15a12cfd32b2d565ff1ea61be231de00dc2a6ecfe55ff92edb97bd4a76`.
- `audit_residual_membership_prereqs.py`
  `9340af619e62a4c4a9aaad715beea822324e7414a7cbfd17e88b341f83537c8f`.

Checks/scope: status check passes handoff-index/manifest declarations only, not
math or full file integrity.  No Lean build was run locally.  `LATEST.md` has
newer run `41008974701` in progress but no result bytes to consume;
`FrozenCapResidualMembership` remains **CI pending/dependency-blocked**.

Still missing: B13/B13Main green hashes and then the consumer exit 0; 382 HOST
payloads; an exclusion-to-`RemainingTerminalRadius` bridge; all energy/class
credit remains unpaid.

Next: when `LATEST.md` exposes run `41008974701` (or its successor), inspect
exits in dependency order.  If B13 is still red, report the precise causal
errors and wait for Lane B rather than editing B13.  If B13/B13Main are green,
CI-check `FrozenCapResidualMembership` unchanged on the same committed tree.
