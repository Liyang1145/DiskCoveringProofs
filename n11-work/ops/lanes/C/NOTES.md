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

## 2026-10-31 - part 202 (conditional 373-id consumer and exact census)

Added `EnergyTerminalBatchB13RefineSixteenResidual.lean`. It defines
`residualIDs` as terminal true, not sharp, and not in
`RefineSixteenRepair.paidIDs`; proves `mem_residualIDs_iff`, `remaining_iff`,
certificate extraction, a certificate-to-repair consumer, a direct consumer to
`EnergyTerminalBatchB13.RemainingTerminalRadius`, and the final chart-radius
consumer. It asserts no cardinality and no residual certificate. Added this
module to `TARGETS.txt` after the repair.

Added `build_residual_census_sixteen.py` and generated
`residual373-conditional-census.json`. It verifies the exact 16 refinement ids
`{37,2337,2341,2965,3040,3112,3116,3431,3440,3573,3589,3623,3633,3777,3792,
3853}` all lie in the frozen 389 census and outputs the 373-id complement with
SHA256 `7539D9214C5CAC780F027688D2BFA41D5451A0D13BA7834BBC49E9D2FAE41A6A`.
This is **conditional** on the repair; it calls no id paid.

Checks run: census emitter exit 0 with exact count 373;
`git diff --check` exit 0; forbidden-token scan of the new Lean module found no
matches. Scope is deterministic host arithmetic and static Lean inspection; no
local kernel claim. SHA256 (lowercase): consumer module
`6b34b72736abb8dc67e6d392098241812a18a206470e78fbd171c259cc39b902`;
emitter `42ee75534f10357e1658941df59f2b4a44eff5a22764a297716b62690d01fd4c`;
census `13024cf1d1cb3ff791b0fdfa21e83cc99d2117b5e8bd3c00f50c9b30009ae5bc`;
`TARGETS.txt` `b4a09cbcb10b870318d15a74e9d9af6959a090421d65066c9fd40b54b2888ed9`.
Both new Lean modules and the 373 reduction are **CI pending**.

Still unproved: every one of the 373 residual radius certificates; geometric
packet/canonical production; the 382 absent payloads; MPacket validity;
seven-class and energy premises; root integration. The repair is a reduction
only. Very next concrete step: read the next `n11-lean-build` summary for
`RefineSixteenRepair` and `RefineSixteenResidual`; fix the first failing
declaration if red. If green, strengthen the conditional census into a proved
Lean `residualIDs.card = 373` and preserve the two consumers unchanged.

ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 203 (conditional 373 Lean census)

Implemented the next step from part 202. Added the deterministic emitter
`emit_residual373_census.py` and generated
`EnergyTerminalBatchB13RefineSixteenResidualCensus.lean`. The module defines
`residual373` in four literal chunks (`100,100,100,73`, separate card checks),
proves the repaired-residual set equals it by 51 source-index blocks of at most
100 symbols, and proves `residualIDs.card = 373` from the chunk cardinalities.
It is **conditional** on `RefineSixteenRepair`; it asserts no radius certificate.
Added `N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus` to
`TARGETS.txt`.

Checks run: emitter exit 0 (373 unique ids, chunk sizes exact);
`git diff --check` exit 0; forbidden-token scan of the generated module found
no matches. Scope is host-side generation plus static inspection, not a local
kernel claim; the full project is not built locally. SHA256 (uppercase):
census module `9717B4E7BA451E2AC3C4B9174893782903760EC92385B127690D2D790B3C4C01`;
emitter `A2DC4221693F155A3C2D573E776B507DE2122A413174264C095917E00F4BC55D`;
`TARGETS.txt` `3AEE3E7292DB9650C334B305BEAC71AD4CB8749CFED7DDCC7C4A173B45911CB5`.
Repair and residual-interface hashes are unchanged from part 202. New census is
**CI pending**.

Still unproved: all 373 radius certificates; packet/canonical production; 382
absent payloads; MPacket validity; seven-class and energy premises; root
integration. Very next concrete step: read CI for `RefineSixteenRepair`,
`RefineSixteenResidual`, and `RefineSixteenResidualCensus`; fix the first failing
declaration if red. If green, apply the residual-certificate interface to the
372-id census after the next independently certified id (do not invent a payment).

ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 204 (independent structural 373 census)

Added `EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff.lean`. It defines
the exact 16 ids added by the repair chain, proves
`RefineSixteenRepair.paidIDs = B13.paidIDs ∪ removedIDs`, and obtains the
repaired residual as `EnergyTerminalResidualCensus.residualIDs \ removedIDs`.
It then proves `removedIDs.card = 16`, the 16 memberships in the 389 census,
and `RefineSixteenResidual.residualIDs.card = 373` by `Finset.card_sdiff`.
This reuses the existing 389 census instead of making 51 fresh 5011-index
decisions against the whole 2013-element paid set. Added
`N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff` to
`TARGETS.txt`. It asserts no radius certificate or mathematical payment.

Checks run: exact host check that `removedIDs` contains 16 unique ids and every
id occurs in the source; `python3 -m py_compile` over all lane-C Python files,
exit 0; `git diff --check`, exit 0; forbidden-token scan of the new module found
no matches. Scope is static source inspection and exact host arithmetic, not a
local kernel claim. SHA256 (lowercase): sdiff census
`e92a1fcc89f71f9ed3f1f2b49186338f9faebde588e10a2a3d5f0211f7125409`;
`TARGETS.txt` `488a504095e92ce92c8316303695892d470405d9ec872a723a4aedc0e94e6de6`.
The module is **CI pending**; the earlier generated census is also still
**CI pending**.

Still unproved: all 373 radius certificates; packet/canonical production; 382
absent payloads; MPacket validity; seven-class and energy premises; root
integration. Both census modules are reductions only. Very next concrete step:
read the next `n11-lean-build` summary for the repair, residual interface, both
census modules, and the sdiff census; fix the first failing declaration if red.
If both census proofs are green, keep the structural sdiff proof as primary and
do not spend more time on cardinality; the remaining work is certificate
production, not census bookkeeping.

ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 205 (resume audit; no new payment)

Re-read the part-204 handoff. `ops/ci/LATEST.md` is still run
`41201323694` (sha `3551ab87`) and predates the repair, residual interface, and
both census modules, so all four remain **CI pending**; there is no new CI
verdict to consume. Rechecked that the structural sdiff module already proves
the required bridge `RefineSixteenResidual.residualIDs =
EnergyTerminalResidualCensus.residualIDs \ removedIDs`, `removedIDs.card = 16`,
and `residualIDs.card = 373`; no duplicate bookkeeping module is needed.

Checks run this part: `python3 -m py_compile` on both new lane-C census
scripts, exit 0 with `PY_COMPILE_OK`; forbidden-token scan over
`EnergyTerminalBatchB13RefineSixteen*.lean`, no matches; no local `.lake`
olean tree exists, so no local Lean/kernel claim. Scope is static source and
host Python only. No file hash changed from part 204.

Still unproved: all 373 radius certificates, canonical/geometric packet
production, 382 non-public payloads, MPacket validity, seven-class and energy
premises, root integration. Very next concrete step: on the next refreshed CI,
check `RefineSixteenRepair`, `RefineSixteenResidual`,
`RefineSixteenResidualCensus`, and `...CensusSdiff` in order; fix the first red
declaration. If green, do not add more census modules: either consume a real
independently certified residual id or mark C mathematically blocked pending
the missing packet producer/data. No ROOT-IMPORT REQUEST.
