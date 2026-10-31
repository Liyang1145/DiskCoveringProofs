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
