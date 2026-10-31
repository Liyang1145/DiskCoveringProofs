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

## 2026-10-31 - part 217 (batch 4; live CI)

Restored the final eight unused token-clean archived split certificates
verbatim from `origin/ci/n11-build` commit `8de79f77`:
`EnergyRefineN{3522,3783,3808,3821,3841,3851,4162,4244}.lean`, with wrappers
from `restore_archive_refinements_batch4.py`. Static scope only. Run
`41222715534` reports `RefineSixteenRepair`/`Residual`/`Sixteen`/`Main` exit 0,
but `RefineSixteenResidualCensus` and the old 389 census exit 1. Batch-2/3/4
targets were not reached.

## 2026-10-31 - part 218 (census failure diagnosed)

Downloaded artifact `n11-build-41222715534` (head `8f861bae`) and read
`summary.json.errors_head`. The census failed at line 41 `No goals to be
solved`, then kernel deep recursion at many per-id `decide +kernel` calls and
deterministic 200000-heartbeat `whnf` timeouts. The failure was proof encoding,
not a false residual id. This diagnosis predates parts 219-220.

## 2026-10-31 - part 219 (census cardinality decomposed)

Replaced the single 373-literal `decide +kernel` in `card_chunks` with six
pairwise chunk-disjointness facts, three union-cardinality rewrites, four
chunk-card facts, and `norm_num`. Regenerated
`n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualCensus.lean`
via `n11-work/ops/lanes/C/emit_residual373_census.py`.
SHA256: Census `9d2a022c4da019957a77a8e7ffbb488cdbc888387d0c811da6b449e626a36894`;
emitter `4501e8292534d47bbdbe6a322d2f759cf82f100a70b6555e9740cb4d1669e63b`.
Static checks only; **CI pending**. The 51 block membership proofs still use
100-id `interval_cases`/`simp` and are the remaining likely timeout risk.

## 2026-10-31 - part 220 (census-independent main consumer)

Added `n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualMain.lean`
(SHA256 `d694a018ec0fb517a914ec0e3c8423367c43d6361a535e1364e7e598b8487261`).
It consumes certificates or packet producers over the **actual**
`RefineSixteenResidual.residualIDs`, so a red literal-census encoding can no
longer block the main interface. Endpoints:
`main_of_residual_radius_certificates_and_seven_classes`,
`full_disk_bound_of_residual_radius_certificates_and_seven_classes`,
`main_of_residual_packet_producers_and_seven_classes`, and
`full_disk_bound_of_residual_packet_producers_and_seven_classes`.
Added the module to `TARGETS.txt` (now 164 unique targets).

Checks (scope: static only; no local project build and no kernel claim):
forbidden-token scan exit 1 with no matches; `git diff --check` exit 0; target
list has no duplicates. The new consumer is **CI pending** and pays no id.

Still unproved: all 373 residual radius certificates; packet
production/canonicality; the other 382 payloads; seven-class and energy
premises; root integration. The 373 literal census remains conditional until
its target exits 0.

Very next concrete step: read the next lane-C artifact for
`RefineSixteenResidualCensus` and `RefineSixteenResidualMain`. If the census
still times out, replace each 100-id block with ten 10-id subtheorems and prove
their union without unfolding the 2013-element paid set; retain the direct
residual-set consumer regardless.

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
