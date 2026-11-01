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

## 2026-11-01 - part 227 (arbitrary-row certificate bridge audit)

Added `audit_anyrow_certificate_bridge.py` and regenerated
`anyrow-certificate-bridge-audit.json` (SHA256 `CC88D851...AC9CE`). The audit
ties `next512-row-cap-certificates.json` to the Lean generic-`m` exclusions:
for all seven public payload ids it exactly matched 63 Lean `y_id` weights,
verified 700 copied `FrozenCapRowCap*.db` entries against `DBMSourceTreeData`,
and rechecked all 700 ordered-pair row caps plus each strict gain with
`Fraction`. All checks passed; minimum cap slacks occur on diagonal rows and
are zero, while every strict gain margin is positive. Certificate JSON SHA256
is `0B50B075...027024B`; core Lean SHA256 `3ED6BB50...FC4E7C4`; frozen DBM
SHA256 `BD4E71CB...EA8ED5`.

Checks: exit 0, byte-stable rerun, `py_compile`, forbidden-token scan, and
`git diff --check` clean. Scope is exact source arithmetic only: **not
CI/kernel credit and no residual id paid**. The seven still lack packet
`f0Lo`/`g`; the other 382 payloads remain absent. Next: apply the same
arbitrary-row search to any newly available payload, and require a completed
CI run on the restored 54-line census.

## 2026-11-01 - part 228 (bounded payload inventory completed)

Found that `audit_residual_repository_payloads.py` silently skipped the 7.6 MB
`evidence-20261028/inputs/paid16-general-next512.json`, the only bounded local
input containing residual records. Raised the parse bound to 10 MB and made the
contract distinguish known from missing payloads. The input contains exactly
the seven known ids `{1409,2337,2341,2356,2360,2368,2370}`; the inventory now
reports `known_payload_count=7`, `missing_payload_count=382`, and a hash over
the missing-382 set.

The only skipped input is the unrelated 39 MB C450 host asset, explicitly listed
in the report. Script SHA256 `2B51750A...F068F027`; report SHA256
`FC3F7894...B890B9`. Checks: inventory contract assertions exit 0, `py_compile`
exit 0, byte-stable rerun, `git diff --check` clean, forbidden-token scan clean.
Scope is repository-local JSON inventory only: **not HOST storage, CI, kernel
credit, or payment**. No new payload is available.

Still unproved: the 373 residual radius certificates (including `f0Lo`/`g`),
382 absent payloads, SevenClassExclusions (0/7), and the arbitrary-centre
theorem. Next: require completed CI for the census; mathematically, obtain a
payload export for one of the 382 or prove its packet directly.

## 2026-11-01 - part 229 (oversized C450 asset parsed exactly)

The 382-missing inventory had left one 39,165,879-byte restored C450 archive
unparsed. Direct inspection showed `results` contains 28 grouped segment packet
tables whose record schema has no `id`, `f0Lo`, or `g` field; apparent numeric
matches were only substrings of exact rational numerators/denominators. Raised
the inventory parse bound to 64 MB and reran it, so this asset is now scanned
rather than described as unrelated.

Report: 773 files / 53,178,301 bytes parsed, 0 oversized files, 7 recovered
payload ids `{1409,2337,2341,2356,2360,2368,2370}`, 382 missing, missing-set
SHA256 `f09a5bc4...5e90`. Script SHA256 `948759AA...07767`; report SHA256
`FDED7A24...E4C82`. Checks: generator exit 0, second run byte-identical,
`py_compile` exit 0, `git diff --check` clean, forbidden-token scan clean.
Scope remains repository-local JSON inventory: **not HOST storage, CI/kernel
credit, or payment**.

Still unproved: the 373 residual radius certificates (including `f0Lo`/`g`),
382 absent payloads, SevenClassExclusions (0/7), and the arbitrary-centre
theorem. Next concrete step: derive a packet directly for one residual id from
the archived source proof data, since no local payload export exists.

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
