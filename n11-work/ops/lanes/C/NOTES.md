# Lane C notes

## Standing constraints

- Kernel credit requires CI exit 0 and a mathematical consumer. Exact rational
  audits, static scans, and hash/tree audits are diagnostics only.
- No `sorry`/`admit`/new `axiom`/`native_decide`/`ofReduceBool`/
  `implemented_by`/`maxHeartbeats 0`; do not edit frozen modules, root,
  lakefile, toolchain, or manifest.
- Preserve green `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`, and `FrozenCapWideFieldWitnesses` unchanged.
- `ExcludedTree` is not a bridge to `RemainingTerminalRadius`. Public exclusion
  tree results are conditional on packet `f0Lo`/`g` and pay no residual id.
- Scan forbidden tokens without relying on `\b` under POSIX `rg`.

## Condensed history

- The frozen B13 census is terminal - sharp - 1997 paid = 389 ids. Only seven
  `{1409,2337,2341,2356,2360,2368,2370}` have public tree payloads; the other
  382 payloads are absent. Row caps exclude those seven for any row count, so
  wider LP work cannot rescue them. Five-field payloads for 2356/2370 remain
  conditional. No residual id is paid.
- CI `41201323694` is green for `RefineFourteen` (`paid_count = 2011`) and
  `RefineFourteenMain`. `41217409382` is green for `RefineSixteenRepair`,
  `RefineSixteenResidual`, `RefineSixteen`, and `RefineSixteenMain`, leaving a
  373-id conditional residual. Those interfaces are equivalences, not payments.
- Earlier census failures were proof-encoding failures, not false ids. A
  one-goal 373-literal `decide +kernel` and 100-id `decide +kernel` blocks both
  exceeded kernel recursion/heartbeat limits. Part 219 split cardinality
  structurally and used four literal chunks.
- Missing throughout: radius certificates for the 373 residual ids;
  canonical/geometric packet production; 382 non-public payloads; MPacket
  validity; seven-class and energy premises; root integration.
- No historical host-side audit or byte check is kernel credit.

## 2026-10-31 to 2026-11-01 - parts 202-226 (condensed)

Added the conditional 373-id interface and several censuses. CI `41217409382`
and `41222715534` were green for repaired residual modules; literal census
targets stayed red from free variables or proof encoding (`No goals`, kernel
recursion, heartbeat limits), not false ids. Five-field Tree bridges use
definitional `rfl`, and producer/residual radius certificates are equivalent.
The structural 54-line census alias (`480a2F78...62DF`) was restored twice;
run `41266567914` exited 143 with no Lean diagnostic. All such targets remain
**CI pending** and pay no id; the seven public records have no arbitrary-row rescue.

## 2026-11-01 - parts 227-229 (condensed certificate/inventory audits)

Part 227 added `audit_anyrow_certificate_bridge.py`; its seven-id exact audit
matched 63 Lean weights, 700 DBM entries, 700 ordered-pair caps, and every
strict gain (report `CC88D851...AC9CE`, certificate `0B50B075...027024B`).
Part 228 exposed the bounded 7.6 MB residual proposal that the inventory had
silently skipped: exactly seven known payload ids and 382 missing. Part 229
raised the parse bound to 64 MB and parsed the 39,165,879-byte C450 archive;
its grouped segment tables have no `id`/`f0Lo`/`g` schema, so it yields no new
payload. Final inventory: 773 files / 53,178,301 bytes, seven known ids, 382
missing (missing-set SHA256 `f09a5bc4...5e90`).

All checks were exit 0, byte-stable reruns, `py_compile`, forbidden-token scan,
and `git diff --check`. Scope is repository-local exact audit/inventory only:
**not HOST storage, CI/kernel credit, or payment**. Still unproved: 373 radius
packets, 382 absent payloads, SevenClassExclusions, and the theorem.
## 2026-11-01 - parts 230-232 (mixture and corrected sign-region LPs)

`PaidCellCertificateMCap` fixes the proposal mixture through `hf0`/`hg`, not
all `beta : Fin 16`. For all seven public records, `cl/f0Lo/g` were exactly
recovered from the 36 packet lines (zero Fraction error). `search_beta_row_lp`
initially omitted the piecewise `endpoint_lo(g)` factors; after correction,
all seven float optima are negative and all exact rounded candidates fail.
Closest is 2356 at `-7.388363184302248e-7`; no rescue, infeasibility proof,
kernel credit, or paid id. Files and full hashes are in parts 231-235 reports
and `beta-row-lp-scaled-results.json`.

## 2026-11-01 - part 233 (2356 active-branch identification)

Added `audit_beta_lp_active_vertex.py` and ran all 512 corrected sign regions
for id 2356. HiGHS selects mask 71 with float optimum `-0.14438698979548076`.
The numerical active-equality selection has 107 rows, but exact `Decimal`
elimination using the original `Fraction` coefficients is singular at column
106. The reconstruction therefore **failed** and produced no beta/lambda/rmin,
no gap claim, and no rescue. This distinguishes a genuinely dependent active
set from the earlier coordinate-rounding failure.

Report `beta-lp-active-vertex.json` records the branch and the exact failure.
Checks: full 512-branch sweep within 65 s, `py_compile` exit 0, forbidden-token
scan clean, `git diff --check` clean. Scope is arithmetic/search only: **not an
infeasibility proof, kernel credit, or payment**. No Lean module or TARGET was
added. Still unproved: all 373 radius packets, 382 absent payloads,
SevenClassExclusions (0/7), and the arbitrary-centre theorem.

Next concrete step: compute an exact `Fraction` RREF of the mask-71 active
rows, add equations for its free variables from the float vertex, and re-solve
the resulting consistent square system; then recheck every reduced row and the
strict gap with `Fraction` before considering the other six ids.

## 2026-11-01 - part 234 (exact LP vertex bug found and repaired)

Found the root cause of part 233's singular active set: the exact equality row
in `audit_beta_lp_active_vertex.py` encoded `beta_8 = 1` (an unbound leaked
`j`) while the float LP correctly used `sum beta = 1`. Corrected that exact row.
Added `audit_beta_lp_exact_rank.py`, which performs Fraction Gauss-Jordan and
reports rank, free columns, augmented inconsistency, and an exact solution.
Added `locate_beta_lp_inconsistent_row.py` as the certificate diagnostic.

For id 2356, mask 71, the corrected active set now has exact rank 107,
is consistent, has no free columns, and is reduced-feasible. Its exact vertex
gap is `-7.388363184123934e-07` (full Fraction in
`beta-lp-exact-rank.json`): **exact negative, no PASS, no residual id paid**.
The old `beta-lp-active-vertex.json` failure is superseded; this session's
exact-rank report is authoritative for the vertex calculation.

Files/SHA256: `audit_beta_lp_active_vertex.py` `0F6D0512...9BB85`;
`audit_beta_lp_exact_rank.py` `8475CD20...F15824`; locator
`47839E61...070C3`; report `19480A03...09F74`; locator report
`EFEB5F77...56C19`. Checks: `py_compile` exit 0 for all edited scripts;
Fraction Gauss-Jordan at tolerances 2e-7 through 1e-12, all rank 107,
consistent, exact-negative; fixed-mask LP and all exact evaluations ran exit 0;
`git diff --check` clean. Scope: exact arithmetic at one float-selected sign
region only, **not an infeasibility proof, CI/kernel credit, or payment**.

Still unproved: all 373 residual radius packets, 382 absent payloads,
SevenClassExclusions (0/7), and the arbitrary-centre theorem. Next concrete
step: use the repaired exact evaluator to reconstruct the best vertices of the
remaining six public ids (optimization in one selected mask per id), checking
whether any exact gap is positive; do not sweep all 512 masks until a positive
float candidate appears.

## 2026-11-01 - part 235 (exact vertices for remaining six public ids)

Added `audit_beta_lp_exact_sweep.py` and ran one best-sign-region LP sweep plus
exact Fraction Gauss-Jordan/recheck for each remaining public record. All six
mask-selected active sets have rank 107, no free columns, exact reduced rows,
and exact-negative gaps: 1409 mask 15 `-3.121634442889577e-05`; 2337 mask 114
`-1.0365427694943543e-05`; 2341 mask 55 `-2.678143522094676e-05`; 2360 mask
247 `-1.7193773513727577e-05`; 2368 mask 98 `-4.965940403282977e-05`; 2370
mask 99 `-3.7366048306710155e-05`. With corrected 2356 this is 7/7 exact
negative at each id's best float sign region; no id is paid. This does not prove
infeasibility over all 512 regions. Files: `audit_beta_lp_exact_sweep.py`
SHA256 `c24bc4190302d488790878de77b78f5269b56a6625e9590768948777edb85536`;
`beta-lp-exact-sweep.json` SHA256
`b25b5f3e0c8d18731f8d10e5851bcd15fcc546ed7dd95201c172219b44b6da61`. Checks:
`py_compile` exit 0; full 512 masks/id and exact rechecks exit 0 (175 s); scans
and `git diff --check` clean. No Lean module/TARGET added.
Still unproved: 373 radius packets, 382 absent payloads, SevenClassExclusions
(0/7), arbitrary-centre theorem. Next: derive a region-independent exact
duality/Farkas certificate, or use the exact evaluator to test all masks for
one representative id rather than treating one negative region as decisive.

Condensed: `audit_beta_lp_all_regions.py` checked all 512 regions of 2356 and
`merge_beta_lp_region_reports.py` combined them: 448 exact-negative vertices,
64 float-infeasible, zero PASS. See `beta-lp-all-regions-combined.json`.

## 2026-11-01 - part 238 (exact Farkas certificates for 2356)

Added `audit_beta_lp_farkas.py`: normalized alternative `y>=0`, z free,
`[A Aeq]^T(y,z)=0`, `[b beq]^T(y,z)=-1`; exact Fraction Gaussian rebuild of
the float support, then exact sign/residual/normalization checks. Full 512-mask
run produced 64 `exact-normalized-Farkas` certificates, exactly the same mask
set as the prior 64 float-infeasible regions (set equality checked); the other
448 alternatives are float-infeasible (primal feasible, not yet bounded below
`T2`). Script SHA256 `05112041...04BE3BC`; report
`beta-lp-farkas-all.json` SHA256 `A6B2359D...D30B23F`.
Checks: `py_compile` exit 0; full run exit 0 in about 54 s; `git diff --check`
clean; forbidden-token scan clean. Scope: one id's sign-region LP infeasibility,
not a global infeasibility result, kernel credit, or residual payment.

Still unproved: threshold bounds for the 448 feasible regions, 373 packets,
382 absent payloads, SevenClassExclusions (0/7), arbitrary-centre theorem.

## 2026-11-01 - part 239 (threshold-Farkas audit; 8 exact regions)

Added `audit_beta_lp_threshold_farkas.py`. It appends the exact row
`lower >= T2` (equivalently `-objective.x <= -T2`) to each sign region and
searches the normalized alternative `y>=0`, z free,
`[A Aeq]^T(y,z)=0`, `[b beq]^T(y,z)=-1`. An exact certificate proves that
this region has no point with `lower >= T2`. The ordinary dual reconstruction
failed on near-tight degenerate supports, so the fallback chooses an L1-vertex
support, selects equations by one pivoted QR, and solves that square system
over Q before rechecking signs/residual/normalization exactly.

Smoke report covers the first eight exact-negative masks
`{4,6,12,14,16,18,20,22}` of id 2356; all eight are
`exact-l1-normalized-Farkas` (82/82/82/82/86/86/82/82 nonzero inequality
multipliers). Script SHA256 `C4D57638...01FD06`; report
`beta-lp-threshold-smoke.json` SHA256 `74A387B6...3B6370`.
Checks: `py_compile` exit 0; smoke run exit 0; forbidden-token scan and
`git diff --check` clean. The earlier 64 region-infeasibility certificates
remain in `beta-lp-farkas-all.json`. Scope: 8/448 negative regions and one id;
**no full 512-region proof, kernel credit, or payment**.

The planned 448-mask run was stopped because exact L1 reconstruction costs about
5-6 seconds per near-tight mask (the first parallel attempt processed only
17 before the session budget). Still unproved: the remaining 440 negative
regions, all 373 packets, 382 absent payloads, SevenClassExclusions (0/7), and
the arbitrary-centre theorem. Next: replace Fraction Gauss-Jordan on the
~100x100 square system with a stable high-precision solve plus exact rational
lifting/recheck (or batch the regions in CI), then merge threshold certificates
for the 448 masks with the existing 64 infeasibility certificates and assert
512/512 exact coverage.

## 2026-11-01 - part 240 (all 512 threshold-Farkas regions for 2356)

Added an optional FLINT exact-rational fast path to `solve_square` in
`audit_beta_lp_farkas.py` and to the L1 solve in
`audit_beta_lp_threshold_farkas.py`, retaining the pure-Python fallback and the
same exact sign/residual/normalization recheck. Reordered the threshold audit
to try the robust L1 reconstruction before the 1.5 s failing primary heuristic.
Full run: all 512 masks returned `exact-l1-normalized-Farkas`, each stored
`y` has 127 entries, and all float LPs succeeded. Report:
`beta-lp-threshold-all.json` (17,049,097 bytes) SHA256
`E4EFBB9B702F50A85BD4900C482AAE09F529416E11D71BEDE32AE7F0E46BA8A5`.
Scripts: threshold SHA256 `52F646CE...676B31D`; shared audit
`DF474472...CF801D`.
Checks: full 512-mask run and `py_compile` exited 0; exact checks are internal.
Scope: each id-2356 sign region cannot attain `lower > T2` in this LP model;
this is not kernel credit, payment of id 2356, or the arbitrary-centre theorem.
Still unproved: six public ids' threshold coverage, 373 radius packets, 382
absent payloads, SevenClassExclusions (0/7), and the arbitrary-centre theorem.
Next: sweep the six remaining public ids, then independently verify every stored
certificate against reconstructed exact rows.

## 2026-11-01 - part 241 (independent 2356 certificate replay)

Added `verify_beta_lp_threshold_reports.py`: it reconstructs each exact LP row
from the proposal/DBM, parses the stored rational multiplier vector, checks all
nonnegative inequality multipliers, all 107 zero-residual columns, exact
normalization `-1`, nonzero counts, source hashes, threshold, mask ordering, and
optional 512-mask completeness. It reuses neither the certificate constructor
nor its solver.

Replayed the complete id-2356 report: all 512 certificates passed exact checks;
report SHA256 `E4EFBB9B702F50A85BD4900C482AAE09F529416E11D71BEDE32AE7F0E46BA8A5`.
Verifier SHA256 `09C653ED...9386DD`; verification report
`beta-lp-threshold-verification-2356.json` SHA256 `A071B85B...CF8F4D`.
Checks: `py_compile` exit 0; full 512 replay exit 0 (about 50 s); forbidden-token
scan and `git diff --check` clean. Scope: exact region-local LP certificates for
one id only, **not kernel credit, a residual payment, or the theorem**.

Six-id sweeps were started but their per-mask cost prevented a saved full run;
the interrupted logs (`threshold-logs/*.log`) are diagnostics only. Still
unproved: threshold coverage for all six remaining public ids, 373 radius
packets, 382 absent payloads, SevenClassExclusions (0/7), arbitrary-centre theorem.
Next: run each six-id report in CI-sized contiguous slices with checkpointing,
then replay all stored certificates with the new verifier.
