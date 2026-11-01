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

## 2026-10-31 - part 221 (literal census de-duplicated)

Diagnosed the census red path from the CI job log for head `bb9fb0c0`: the
51 `decide +kernel +revert` blocks spent 142s and were OOM-guarded at
14,816,320 KB. The earlier run `41229638083` had failed at line 49 with
`Expected type must not contain free variables`. This was a proof-encoding
blowup, not a census discrepancy.

Replaced the duplicated 373-literal census in
`n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualCensus.lean`
with a 49-line structural alias of
`EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs` (389 census
minus the literal 16 refinements). It retains `residualIDs_eq_residual373`,
`residual373_card = 373`, `residualIDs_card = 373`, and both conditional
radius-certificate consumers. No kernel decision over the paid set remains.
SHA256: Lean `3308DADD...DFB0C1D`; emitter `B36087FE...1178E53`.

Regenerated with `n11-work/ops/lanes/C/emit_residual373_census.py` from the
committed exact JSON (373 unique ids). Checks run: emitter exit 0; forbidden
token scan clean; regeneration byte-stable; `git diff --check` exit 0. Exact
source comparison confirms the `paidIDs` definitions in `RefineSixteen` and
`RefineSixteenRepair` have identical bodies, so the alias's `rfl` is a
definitional-unfolding step. Scope is static source/byte inspection only:
**CI pending**, no radius paid and no kernel claim.

Still unproved: the 373 residual radius certificates, packet `f0Lo`/`g`, the
382 absent payloads, SevenClassExclusions (0/7), and arbitrary-centre
full-disk theorem. The new target also depends on the upstream lane-B
`EnergyTerminalResidualCensus`/`RefineSixteen` targets, currently CI red.

Next: after supervisor commit, require `RefineSixteenResidualCensus` and
`RefineSixteenResidualCensusMain` to exit 0 and record whether any failure is
in this alias or its upstream structural census. Do not restore literal
per-index kernel enumeration.

## 2026-10-31 - part 222 (alias dependency made explicit)

Checked the two paid-set definition bodies directly:
`EnergyTerminalBatchB13RefineSixteenRepair.paidIDs` and
`EnergyTerminalBatchB13RefineSixteen.paidIDs` are identical. Added
`repair_paidIDs_eq_refineSixteen_paidIDs` to the generated census alias and
used that equality explicitly in `residualIDs_eq_residual373`, rather than
depending on an unstated definitional unfolding. Regenerated with
`n11-work/ops/lanes/C/emit_residual373_census.py`; file stays 54 lines.

SHA256: Lean `480a2f78432d6400455f4a84f3dab2c4f838057ac8b05370959070975a8c62df`;
emitter `b048873b43dea935314a9cc273026576a54fce7251c0f807a00da631c25ca52e`.
Checks (static only): regeneration exit 0 and byte-stable; forbidden-token scan
clean; `git diff --check` exit 0. A 45s isolated `/workspace/tools/mathlib-probe`
pattern probe timed out with no output, so no kernel claim is made from it.
`RefineSixteenResidualCensus`/`CensusMain` remain **CI pending**.

Still unproved is unchanged: 373 residual radius certificates, packet
`f0Lo`/`g`, 382 absent payloads, SevenClassExclusions (0/7), and the
arbitrary-centre full-disk theorem. Next: read CI for these two targets after
the supervisor commit; attribute any red result to this alias or its upstream
structural census, and do not reintroduce literal per-index enumeration.

## 2026-10-31 - part 223 (CI attribution and alias revalidation)

Read `ops/ci/LATEST.md`: run `41229638083` reports
`RefineSixteenResidualCensus`/`CensusMain` exit 1, but its recorded error is
at line 49 of the **committed** 573-line literal version (`decide +kernel
+revert`), not the 54-line structural alias now in this worktree. That run
therefore supplies no verdict on parts 221-222. The same artifact also shows
the unrelated `SharedMomentConcreteSwitchBatch` target OOM-guarded by the
memory watch; do not attribute that failure to lane C.

Rechecked all alias dependencies against source: `refinedResidualIDs`,
`refinedResidualIDs_card`, `mem_refinedResidualIDs_iff`,
`RefineSixteenResidual.mem_residualIDs_iff`, and both residual-certificate
consumers exist with the referenced types. The non-repaired and repaired
`paidIDs` bodies are still byte-identical in their defining expressions.
Regeneration via `emit_residual373_census.py` exited 0, produced 54 lines and
373 ids structurally, gave Lean SHA256
`480a2f78432d6400455f4a84f3dab2c4f838057ac8b05370959070975a8c62df` and
emitter SHA256
`b048873b43dea935314a9cc273026576a54fce7251c0f807a00da631c25ca52e`.
Forbidden-token scan and `git diff --check` are clean. Scope remains static
source/byte validation: **CI pending**, no kernel or payment claim.

Unproved obligations remain the 373 residual radius certificates, packet
`f0Lo`/`g`, 382 absent payloads, seven-class exclusions (0/7), and the
arbitrary-centre theorem. Next concrete step: after the supervisor commits
parts 221-223, read the fresh census/`CensusMain` exits. If green, mark the
conditional 373-cardinality interface CI-green; if red, inspect only the new
54-line alias first and preserve its upstream dependency attribution.

## 2026-10-31 - part 224 (merge regression repaired)

Found a merge regression: lane-B commit `cf185b5b` replaced lane C's 54-line
structural alias with a 733-line literal census. Downloaded the log for Lean
run `41248242451` (head `1a300c5e`): `RefineSixteenResidualMain` exited 0, but
`RefineSixteenResidualCensus` exited 1 at lines 49/51 with `Expected type must
not contain free variables`; `CensusMain` then exited 1 on the same dependency.
This is the old literal encoding failure and does not falsify any residual id.

Restored the alias through `n11-work/ops/lanes/C/emit_residual373_census.py`.
Lean SHA256 is again
`480a2f78432d6400455f4a84f3dab2c4f838057ac8b05370959070975a8c62df`
(54 lines); emitter SHA256 is
`d9fcd1c7bc802e594d1200e75a45c3004beccc344746f913ba8452ae9218288d`.
The emitter now records both the earlier OOM and the free-variable failure.
Checks: emitter exit 0; exact JSON has 373 unique ids; regeneration is
byte-stable; `git diff --check` clean; forbidden-token scan clean except the
intentional `#print axioms` audit commands. Scope is static source/hash plus
external CI-log inspection: repaired census and `CensusMain` are **CI pending**.

Still unproved: the 373 residual radius certificates, packet `f0Lo`/`g`, 382
absent payloads, SevenClassExclusions (0/7), and the arbitrary-centre theorem.
Next: after the supervisor commit, require both census targets to exit 0; if
the literal census reappears, reject the merge rather than re-running its 51
free-variable blocks.

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
