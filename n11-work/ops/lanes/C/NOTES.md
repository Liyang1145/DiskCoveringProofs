EXPERT (2026-10-31):
- Seven green row caps prove only `not_valid_of_frozen_cap`; they are conditional exclusions, not energy payment.
- First CI the fixed TreeBridges, PublicExcludedTree, and Aggregate; green there advances no residual count.
- Stop expanding row caps. State the missing packet producer: feasible `r < sourceRadius` yields a packet with the frozen node, `f0Lo`, and `g`.
- Add a real consumer first, e.g. `ResidualRadiusCertificate n` plus `remaining_of_residual_certificates` over `EnergyTerminalBatchB13.residualIDs`.
- Corrected 4-field witnesses cover only 1409/2337/2341; the 2368 five-field candidate and empty 2370 timeout are not Lean credit.
- If the producer/canonicality implication cannot be proved, mark C blocked; do not rename `RemainingTerminalRadius` as an axiom or structure field.

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

## Condensed prior history (through part 201)

- The frozen B13 census is terminal - sharp - 1997 paid = 389 ids. Only seven
  `{1409,2337,2341,2356,2360,2368,2370}` have public tree payloads; the other
  382 payloads are absent. Public row caps exclude those seven for any row
  count, so 10/12/16-row LP work cannot rescue them. Five-field payloads for
  2356/2370 remain conditional and incomplete; no id is paid.
- CI run `41201323694` is green for `EnergyTerminalBatchB13RefineFourteen`
  (`paid_count = 2011 = 1997 + 14`) and `RefineFourteenMain`, so the open B13
  residual is 375. It is also green for the residual certificate interface and
  its B13 consumers. Those interfaces are equivalences, not payments.
- The same run reddened `RefineSixteen` at line 31 with elaborator recursion
  depth, not a failed radius certificate. Part 201 added
  `EnergyTerminalBatchB13RefineSixteenRepair.lean`, with scoped
  `maxRecDepth 10000`, disjointness, `paid_count = 2013`, `paid_radius`, and
  `remaining_of` to B13. It was **CI pending** at the start of this part.
- Missing throughout: radius certificates for the 375/373 residual ids;
  canonical/geometric packet production; 382 non-public payloads; MPacket
  validity; seven-class and energy premises; root integration.
- No historical host-side audit is kernel credit.

## 2026-10-31 - parts 202-208 (condensed: residual interface, census, repairs)

- Part 202 added the conditional 373-id residual interface and exact census;
  part 203 generated the 51-block Lean census; part 204 added a structural sdiff
  census. These reduce bookkeeping only and pay no radius id.
- Part 207's live run `41217409382` was **CI green** for `RefineSixteenRepair`,
  `RefineSixteenResidual`, `RefineSixteen`, and `RefineSixteenMain`.
- The generated census was red on every block at "Expected type must not contain
  free variables"; part 207 changed the block decisions to
  `decide +kernel +revert`. The sdiff census was withheld because imported lane-B
  `EnergyTerminalResidualCensusC01-C04` has the same red `decide` shape.
- `FrozenCapFiveField2368/2370` were green, but their Tree wrappers failed to
  transport `FrozenCapRationalCore.Dq/DQ/T` to the `FlashCosine` names. Part 207
  attempted explicit `norm_num` bridges; part 209 replaces these with `rfl`.
- Part 206 re-ran the public five-field byte audit (702 files, 51,466,284 bytes)
  and both emitters with byte-identical output. Host arithmetic only, no kernel
  claim. No residual id is paid and the census/repair remains conditional.

## 2026-10-31 - part 209 (definitional bridge repair; CI pending)

Replaced the three `norm_num` rational bridges in both
`FrozenCapFiveField2368Tree.lean` and `FrozenCapFiveField2370Tree.lean` with
kernel definitional `rfl` proofs. The definitions are byte-for-byte identical:
`FrozenCapRationalCore.Dq/DQ` unfold to the same `Lq/LQ` and
`RatInterval.piHi/piLo` literals as `FlashCosine.Dq/DQ`, and both `T`s are the
same rational literal. This addresses the part-207 red bullet without invoking
large-denominator arithmetic. No theorem statement, cap, payload, or payment
changed.

Checks run: `git diff --check` exit 0; static line inspection confirms both Tree
wrappers use `rfl` for `hDq`, `hDQ`, and `hT`; exact definitional source
comparison. Scope is static Lean inspection only; both Tree wrappers remain
**CI pending** because the live Actions query was empty and no post-part-207 run
exists. SHA256 (lowercase): Tree2368
`75af2e93c5e81542dfec53b35f0c6f0f527e5cc8d0f47af31ceb353430ede54a`;
Tree2370 `b56b7f22bd0312e8760334fc33fca2310d1551785fe1a5be66cd0cd25e622656`.
A 30-second isolated `lake env lean` probe of the `rfl` principle timed out (exit 124), so it supplies no kernel evidence; the project was not built locally.

Still unproved: all 373 residual radius certificates, packet/canonical
production, 382 absent payloads, seven-class/energy premises, root integration.
Very next concrete step: inspect the next CI result for the two Tree wrappers;
if green, stop row-cap work and mark C blocked pending the packet producer/data
(no ROOT-IMPORT REQUEST). If red, read the exact failing bullet and replace only
that bridge.

## 2026-10-31 - part 210 (CI artifact audit; promotion of census target)

Queried live run `41217409382` (head `068914fb`, workflow conclusion `success`)
and downloaded artifact `n11-build-41217409382`. The run badge is not a
kernel verdict: `summary.json` has exit `1` for both Tree wrappers (old
`simpa` at line 32, type mismatch after simplification) and for the three
census modules (`No goals to be solved` plus free-variable `decide`). The two
`rfl` Tree repairs and the census `+revert` repair are present in the current
worktree but have no post-repair artifact yet, so both remain **CI pending**.
No residual id is paid by this audit.

Moved `EnergyTerminalBatchB13RefineSixteenResidualCensus` to the front of
`TARGETS.txt`, immediately after its residual dependency, so the repaired
census is reached before the long refinement list. Host census cross-check:
389 frozen residual ids, 16 removed by `RefineSixteenRepair`, 373 conditional
remaining; public payload audit has 7 records and 382 missing. These are
bookkeeping counts, not proof.

Checks: GitHub Actions API query exit 0 and archive extraction exit 0; artifact
target exits inspected above; `git diff --check` exit 0. A 120-second isolated
`lake env lean` tactic probe in `/workspace/tools/mathlib-probe` timed out
(exit 124), so it gives no kernel evidence. Project modules were not built
locally.

Still unproved: all 373 residual radius certificates, the canonical packet
producer (including packet existence at frozen node with `f0Lo`/`g`), 382
absent payloads, seven-class/energy premises, and root integration. Very next
concrete step: let CI run on the current tree; inspect `summary.json` for
`FrozenCapFiveField2368Tree`, `FrozenCapFiveField2370Tree`, and
`EnergyTerminalBatchB13RefineSixteenResidualCensus`. If all exit 0, mark C
blocked on the producer/data (no ROOT-IMPORT REQUEST); if any remains red,
repair only its reported line.

## 2026-10-31 - part 211 (373-census repair and consumer; CI pending)

Diagnosed the new 373 census reds from run `41217409382`: the older, green
389 census uses plain `decide +kernel`, while the new file added `+revert` to
all 51 block proofs. The artifact reports `Expected type must not contain free
variables` at the resulting decisions. Removed `+revert` by restoring the
deterministic emitter as the source of truth. Also removed the trailing
`norm_num` after the cardinality rewrite: the numeral additions reduce
definitionally, so CI reported `No goals to be solved` there.

Added the first real consumer of the repaired census:
`remaining_of_residual373_radius_certificates` and
`b13_remaining_of_residual373_radius_certificates`. These take a
`ResidualRadiusCertificate` for every member of the literal `residual373` set
and compose the existing residual interface to the repaired and original B13
`RemainingTerminalRadius` obligations. This is an interface/consumer theorem,
not payment: no certificate is supplied.

Files: `n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualCensus.lean`
(579 lines, 373 ids) and its emitter
`n11-work/ops/lanes/C/emit_residual373_census.py`. SHA256 (lowercase):
Lean `16ee97f14ff067f3f26195c2e7929473a4191d81e0bd244dc157510be71c846b`;
emitter `3859dfe457ca1e8fcb6d3a4dac5a6f3c24430bc40525a020f0b8df980f5e8f51`.

Checks: emitter rerun exit 0 and produced the stated 579-line file; Python
assertions confirmed no `+revert`, no trailing `norm_num`, and both consumer
names; forbidden-token scan found zero `sorry`/`admit`/`native_decide`/
`maxHeartbeats 0`/`implemented_by`/`ofReduceBool`; `git diff --check` exit 0.
Scope is emitter/static inspection only. A bounded Mathlib probe tested the
generic interval-cases patterns, but does not build project dependencies. The
module remains **CI pending**.

Still unproved: all 373 residual radius certificates, canonical packet
production/existence with the frozen `f0Lo`/`g`, 382 absent payloads,
seven-class/energy premises, and root integration. No id is paid. Very next
concrete step: inspect the next artifact for this target and the two Tree
wrappers; if green, stop interface work and mark C blocked on the missing
packet producer/data (no ROOT-IMPORT REQUEST).

## 2026-10-31 - part 212 (literal-373 endpoint consumer; CI pending)

Added `EnergyTerminalBatchB13RefineSixteenResidualCensusMain.lean`, a separate
main-thread consumer which avoids touching the pending census repair.  It proves
four conditional endpoints from the literal `residual373` census:
`main_of_residual373_radius_certificates_and_seven_classes`,
`full_disk_bound_of_residual373_radius_certificates_and_seven_classes`, and the
two corresponding theorems taking the explicit `ResidualPacketProducer` family.
The packet-producer versions use
`residual_radius_certificate_of_packet_producer`; they do not assume packet
existence.  `SevenClassExclusions` remains explicit.  Added the module to
`TARGETS.txt` immediately after its census dependency.

Checks: `git diff --check` exit 0; forbidden-token scan exit 1 (no matches);
static import/name counts confirmed all four referenced declarations.  Scope is
source inspection only: the module is **CI pending** and no Lean kernel result
was obtained locally.  The latest `n11-lean-build` run is on old head `8f861bae`;
the completed run on head `335d6b13` is `Scoped mathematical replay`, not the
Lean build.  The earlier artifact remains red on the old census `+revert` form.

SHA256 (lowercase): CensusMain
`569fb93edf013085d33caf10981a012a1c8c2c0eb8de9afb76f9b3d73e68b268`;
repaired Census `16ee97f14ff067f3f26195c2e7929473a4191d81e0bd244dc157510be71c846b`;
emitter `3859dfe457ca1e8fcb6d3a4dac5a6f3c24430bc40525a020f0b8df980f5e8f51`.

Still unproved: every one of the 373 `ResidualRadiusCertificate`s (equivalently
the 373 packet producers), the canonical/geometric packet construction, the
382 absent public payloads, the seven named class exclusions, and root
integration.  No residual id is paid.  Very next concrete step: inspect the next
`n11-lean-build` artifact for the repaired Census and CensusMain.  If both are
green, mark C blocked on packet-producer/data completion; if red, repair only
the reported declaration and do not expand row caps.

## 2026-10-31 - part 213 (current-head CI identity; still CI pending)

Re-ran `emit_residual373_census.py` with a timeout: exit 0, 579 lines, 373 ids;
the emitted census hash remains `16ee97f14ff067f3f26195c2e7929473a4191d81e0bd244dc157510be71c846b`
and the emitter hash remains `3859dfe457ca1e8fcb6d3a4dac5a6f3c24430bc40525a020f0b8df980f5e8f51`.
CensusMain remains `569fb93edf013085d33caf10981a012a1c8c2c0eb8de9afb76f9b3d73e68b268`.
Forbidden-token scan found none in the two Lean modules or emitter;
`git diff --check` exited 0.  `TARGETS.txt` includes both Census and CensusMain.
Scoped name audit found the imported `main_of_energy_b13_and_seven_classes`,
`strongInterface_of_n11_main`, and `SevenClassExclusions`, plus both Census
consumer names; this remains static inspection, not elaboration.

CI identity checked through the public Actions API.  Branch head `335d6b13`
has run `41225866222` (`Scoped mathematical replay`, success) and
`41225866243` (`Delivery bytes, not mathematical proof`, failure).  Neither
is the n11 Lean build.  The last Lean artifact is run `41217409382` on the
older tree, before the `+revert` repair.  The local C changes are uncommitted
(`Census.lean`, `TARGETS.txt`, emitter, NOTES, plus new CensusMain), so there
is **no CI evidence** for the repaired census or its consumer.

Scope: emitter/static checks and CI metadata only; no kernel result.  Still
unproved: all 373 radius certificates, canonical packet production, 382 absent
payloads, seven-class/energy premises, and root integration.  No id is paid.
The producer is not a weaker escape: `residual_packet_producer_iff_residual_radius_certificate`
already proves the explicit producer equivalent to the radius obligation.
Very next concrete step: after the supervisor commits, require the next
`n11-lean-build` summary to report exit 0 for Census and CensusMain; if green,
mark C blocked on packet data/producer, otherwise repair only its reported line.

## 2026-10-31 - part 214 (consumer dependency audit; still CI pending)

Audited `EnergyTerminalBatchB13RefineSixteenResidualCensusMain.lean` against
its exact dependency declarations.  The four endpoints consume respectively
`Census.b13_remaining_of_residual373_radius_certificates`,
`EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes`,
`strongInterface_of_n11_main`, and
`EnergyTerminalBatchB13.residual_radius_certificate_of_packet_producer`.
Their argument and result types match the consumer bodies; the two packet
endpoints still assume, rather than prove, the producer premise.

Checks: file/hash recheck confirms CensusMain
`569fb93edf013085d33caf10981a012a1c8c2c0eb8de9afb76f9b3d73e68b268` and
Census `16ee97f14ff067f3f26195c2e7929473a4191d81e0bd244dc157510be71c846b`;
forbidden-token scan returned no matches; `git diff --check` exit 0.  Scope is
static source inspection only; no elaboration or kernel check.  No id is paid.
Still unproved: all 373 radius certificates/producers, canonical packet
production, 382 absent payloads, seven-class/energy premises, root integration.
Very next concrete step: inspect the supervisor's next `n11-lean-build`
artifact for Census and CensusMain; if green, stop interface work and mark C
blocked on packet producer/data; if red, repair only the reported line.
