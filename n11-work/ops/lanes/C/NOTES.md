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

## 2026-10-31 - parts 202-208 (condensed)

Parts 202-204 added the conditional 373-id interface, exact/51-block/sdiff
censuses. Run `41217409382` was green for repaired modules, but the generated
census was red ("Expected type must not contain free variables"); sdiff was
withheld due to the same lane-B C01-C04 `decide` shape. Part 206 re-ran the
five-field byte audit (702 files, 51,466,284 bytes) and both emitters
byte-identically; host arithmetic only.

## 2026-10-31 - parts 209-214 (condensed)

Five-field Tree bridges switched to definitional `rfl`; repaired 373 census
removed an erroneous `+revert` and trailing `norm_num`. Added literal-373
consumers and `RefineSixteenResidualCensusMain` with four endpoints. These
compose premises and pay no id. Exact <5-field host search found no rescue for
the seven public records. Producer and residual radius certificates are proved
equivalent, so the geometric producer remains the real analytic obligation.

## 2026-10-31 - parts 217-220 (condensed)

Batch 4 restored eight archived split certificates from `8de79f77`; run
`41222715534` was green for `RefineSixteenRepair`/`Residual`/`Sixteen`/`Main`
but the literal census was red. Artifact inspection attributed that red to
proof encoding (`No goals`, kernel recursion, and 200000-heartbeat timeouts),
not false residual ids. Part 219 split cardinality; part 220 added
`EnergyTerminalBatchB13RefineSixteenResidualMain.lean`, the direct consumer of
the actual residual set. All remained **CI pending** and paid no id.

## 2026-10-31 - parts 221-224 (condensed)

The literal 373-id census repeatedly OOMed/free-variable-failed; restored the
54-line structural alias (`480a2F78...62DF`) with explicit paid-set equality.
Run `41248242451` was red only in that literal encoding, not in
`RefineSixteenResidualMain`. These targets remain **CI pending** and pay no id.

## 2026-11-01 - parts 225-226 (condensed)

Commit `a30e76db` again replaced the 54-line structural census; it was
regenerated (SHA256 `480a2F78...62DF`). Run `41266567914` exited 143 after a
runner shutdown, 77 s into the census target and with no Lean diagnostic, so it
is neither a pass nor a failure. `ResidualCensus`/`CensusMain` remain **CI
pending**; the seven public records still have no arbitrary-row rescue.

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

## 2026-11-01 - part 236 (exact all-region sweep begun on 2356)

Added `audit_beta_lp_all_regions.py`, which solves the float LP in each sign
region, reconstructs its active system, performs exact Fraction Gauss-Jordan,
and exactly rechecks any full-rank candidate. It supports bounded resumable
`--start-mask/--stop-mask` runs and `--out` checkpoints.

A 180 s run on id 2356 tested masks 0-103 (30 float-infeasible, 74 exact
negative, 0 PASS); only mask 104 hit the time budget. Thus no positive exact
candidate was found in 104/512 regions, but this is **not** a global
infeasibility proof, kernel credit, or payment. Script SHA256
`2b6e9b1b8a0101ce3c35e2afc8aa719b37106d6cc977875cfa355fa98ae60c8c`;
report `beta-lp-all-regions.json` SHA256
`6339cbbeaf44f678c03e9e98f2a0c101cc5555b3bc702f4843a5a9be7a57530d`.
Checks: `py_compile` exit 0, forbidden-token scan clean, `git diff --check`
clean, exact arithmetic throughout the reported regions.

Still unproved: 373 radius packets, 382 absent payloads, SevenClassExclusions
(0/7), and the arbitrary-centre theorem. Next: resume 2356 at
`--start-mask 96 --out beta-lp-all-regions-96.json` (overlap validates
determinism), then cover the remaining ranges and combine counts.
