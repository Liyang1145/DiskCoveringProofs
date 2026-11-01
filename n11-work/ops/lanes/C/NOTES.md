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

Part 202 added the conditional 373-id residual interface and exact census;
part 203 generated the 51-block Lean census; part 204 added a structural sdiff
census. Part 207's run `41217409382` was green for the repaired modules. The
generated census was red at "Expected type must not contain free variables";
the sdiff census was withheld because imported lane-B C01-C04 had the same red
`decide` shape. Part 206 re-ran the five-field byte audit (702 files,
51,466,284 bytes) and both emitters byte-identically; host arithmetic only.

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
## 2026-11-01 - part 230 (mixture-space audit begun)

New distinction found: `PaidCellCertificateMCap` exclusions fix the proposal
mixture through `hf0`/`hg`; they are not exclusions over all `beta : Fin 16`.
For all seven public records I recomputed `W_k = sum_f beta_f*weight_fk/10^12`
and exactly recovered the stored `cl`, `f0Lo`, and all nine `g_q` from the
record's 36 packet slopes/intercepts (7/7 records, zero Fraction error). This
confirms `beta` is the only untested packet coordinate when lines are frozen.
Committed as `audit_mixture_coordinates.py` plus
`mixture-coordinate-audit.json`; script SHA256 `A20E2AE4...ED22D`, report
SHA256 `8A151A6C...D395B`. Nonzero beta supports are respectively 4,4,5,5,6,4,4.

A bounded scipy/HiGHS formulation (beta simplex, 90 dual rows, rmin, all
`cl`/`g` sign regions) was attempted, but the first run selected rows with
negative DBM entries and returned an invalid "lower" around 1310, far outside
`f0Lo+[-lamB]+rmin` bounds. It is a formulation/search diagnostic only, **not
a rescue or exact certificate**. No new Lean module or TARGET was added.

Checks: auditor exit 0 twice with byte-identical report, `py_compile` exit 0,
and `git diff --check` clean; exact `Fraction` reproduction of `cl/f0Lo/g` on
all seven; DBM rows contain negative entries; local `numpy/scipy` was used for
search only.
Scope is exploratory arithmetic, not kernel credit. Still unproved: all 373
radius packets, 382 absent payloads, seven-class exclusions, and the theorem.
Next: restrict the beta LP to cell-valid dual rows (or add a proof-safe bound
per row), enumerate the sign regions, then exactly recheck any positive gap
with `Fraction` before emitting Lean.

## 2026-11-01 - part 232 (corrected endpoint scale: no public rescue)

Found and corrected a formulation error in `search_beta_row_lp.py`: its reduced
rows used `rmin <= g + rho`, omitting the piecewise `endpoint_lo(g)` factors
`Dq`/`DQ`. The four previously reported positive float gaps were therefore
spurious. Added `search_beta_row_lp_scaled.py`, which enumerates the same 512
`cl`/`g` sign regions but uses `endpoint_lo(g)*beta + rho` exactly, then
rationalizes the winning float candidate and rechecks all nine reduced rows,
`f0Lo`, `cl`, and `T^2` with `Fraction`.

All seven public records have negative corrected float optima. Exact rounded
candidates remain reduced-feasible but all fail the strict gap (decimal gaps):
`1409 -3.121634442889686e-5`, `2337 -1.036542769494521e-5`,
`2341 -2.678143522094817e-5`, `2356 -7.388363184302248e-7`,
`2360 -1.719377351373577e-5`, `2368 -4.965940403283213e-5`,
`2370 -3.736604830672129e-5`. The closest record is still negative; this is a
float-candidate plus exact-recheck diagnostic, not an infeasibility proof or
kernel credit.

Files: `search_beta_row_lp_scaled.py` SHA256
`8091D5EC...A316`; `beta-row-lp-scaled-results.json` SHA256
`E449A3DE...01BC`. Checks: 512 branches for each of seven ids, `py_compile`
exit 0, `git diff --check` clean, forbidden-token scan clean. No Lean module or
TARGET added; paid ids remain 0.

Still unproved: all 373 residual radius packets, the 382 absent payloads,
SevenClassExclusions (0/7), and the arbitrary-centre theorem. Next: solve the
active set of the corrected 2356 LP over `Fraction` (support zeros plus tight
scaled rows) to confirm the exact vertex gap; generalize this exact-vertex
recovery to all 512 regions before drawing any infeasibility conclusion.

## 2026-11-01 - part 231 (beta/row sign-region LP)

Added `search_beta_row_lp.py` and `beta-row-lp-results.json`. For each of the
seven public residual ids the script enumerates all 512 `cl`/nine-`g` sign
regions and solves a bounded SciPy/HiGHS LP over 16-simplex `beta`, 90
nonnegative ordered-pair dual rows, and `rmin`. It then reconstructs `rmin` as
the exact minimum reduced-row RHS and exactly rechecks `f0Lo`, all `g`,
reduced rows, and `T^2` with `Fraction`.

Result: 0 exact PASS. The float optimum is positive for ids
`{2337,2341,2356,2360}` by `6.74e-5`, `1.68e-5`, `1.86e-4`, `1.39e-4`,
but rational reconstruction from `float.limit_denominator` loses every one;
exact gaps are respectively `-4.99e-4`, `-2.69e-4`, `-4.39e-4`, `-3.30e-4`.
For `{1409,2368,2370}` even the float optima are negative. All seven exact
candidates satisfy reduced rows. This is a search diagnostic, not an
infeasibility proof and not kernel credit.

Script SHA256 `7B324F1C...CC600E`; report SHA256 `FF37163F...AEF4D`.
Checks: all 512 branches/record, `py_compile` exit 0, forbidden-token scan
clean. Scope is exact recheck of one rationalized optimum per sign region.
Still unproved: all 373 packets, 382 payloads, seven classes, and theorem.
Next: solve the active-set LP exactly over `Fraction` for the four positive
float regions, rather than rationalizing the full 107-vector, then emit a
packet only if every reduced row and the strict numeric gap survive.

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
