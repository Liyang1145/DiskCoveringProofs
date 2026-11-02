# Lane C notes

## Standing constraints

- Kernel credit requires CI exit 0 and a mathematical consumer. Exact rational
  audits, static scans, and hash/tree audits are diagnostics only.
- No `sorry`/`admit`/new `axiom`/`native_decide`/`ofReduceBool`/
  `implemented_by`/`maxHeartbeats 0`; do not edit frozen modules, root,
  lakefile, toolchain, or manifest.
- Preserve green `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`, and `FrozenCapWideFieldWitnesses` unchanged.
- `ExcludedTree` is not a bridge to `RemainingTerminalRadius`; it pays no id.
- Scan forbidden tokens without relying on `\b` under POSIX `rg`.

## Condensed history

- The frozen B13 census is terminal - sharp - 1997 paid = 389 ids. Only seven
  ids have public tree payloads; the other 382 are absent. Row caps exclude
  those seven for any row count, so wider LP work cannot rescue them. No id paid.
- CI `41201323694` is green for `RefineFourteen` (`paid_count = 2011`) and
  `RefineFourteenMain`. `41217409382` is green for `RefineSixteenRepair`,
  `RefineSixteenResidual`, `RefineSixteen`, and `RefineSixteenMain`, leaving a
  373-id conditional residual. Those interfaces are equivalences, not payments.
- Earlier census failures were proof-encoding, not false ids. Large literal
  `decide +kernel` blocks exceeded kernel limits; cardinality is now structural.
- Missing throughout: radius certificates for the 373 residual ids;
  canonical/geometric packet production; 382 non-public payloads; MPacket
  validity; seven-class and energy premises; root integration.
- No historical host-side audit or byte check is kernel credit.

## 2026-10-31/11-01 - parts 202-245 (condensed)

Inventory: 773 files, 7 public payloads, 382 missing (SHA `f09a5bc4...5e90`).
All seven proposals have exact 512/512 threshold-Farkas coverage but
exact-negative best float gaps. Source audit: 62/389 ids have complete source,
327 missing; report `ddee740b...e03f`. These are audits, not kernel credit.

## 2026-11-01 - part 246 (serialize residual census; CI OOM diagnosis)

CI run `41318867156` OOM-killed the four independent census parts at 7.3-8.6 GB
RSS each. They were made a serial `C01 -> C02 -> C03 -> C04` import chain with
proof bodies byte-unchanged; this was a resource repair, not a census theorem.
Scope was static scheduling only (**CI pending**), with no local kernel check.

## 2026-11-01 - parts 247-248 (N39 restoration and scheduling)

Restored archive id 39 (K=13), dropping only its unbounded heartbeat directive;
archive hash `959ec36e...5ae2`, restored `EnergyRefineN0039` hash
`5bbe2fdb17bff213685e3eab77e0ee35267aa2b54a8e0a8fc914599f45f29a3d`.
Conditional singleton wrapper/main hashes are `407b62f6...a6090` and
`cfb72df3...f8f1b`. Static checks were clean; target ordering placed this tuple
first, but this paid no id. Scope was **CI pending**, with archive validity,
327 source-missing ids, exclusions, and the arbitrary-centre theorem unproved.

## 2026-11-02 - parts 249-252 (N39 repair; structural census start, condensed)

Generated `EnergyRefineN0039Repair.lean` (`42cf57bf...fe472d`), replacing only the
timing-out `pk_ok` tactic. Census work moved to structural membership/cardinality
proofs. No id paid; checks were static/exact-set only and **CI pending**.

## 2026-11-02 - parts 253-258 (389 -> 377 exact interfaces, condensed)

Added structural bridges `RefineTriple` (387), `Refine385`, `Refine378`, and
`Refine377`. They remove, respectively, ids `{37,3149}`, `{37,3112,3149,3853}`,
`{3116,3431,3573,3777,2337,2341,3633}`, and `{3841}` from the kernel-counted
389 census, preserving an exact membership iff, exact cardinality, and a
conditional map from residual radius certificates to `EnergyTerminalBatchB13`.
Sources hashes: 378 `5b119359...61bd4`; 377 `50df6236...76102`.
Each parent target remains CI-unchecked. `verify_census_378.py` passes its exact
389->378 complement and static-token/unique-target audit. No certificate or id
was added or paid.

## 2026-11-02 - parts 259-264 (389 -> 368, condensed)

Serial structural bridges reduce the 389 census through 376, 375, 373, 371,
and 368 by removing green singleton ids `{3792}`, `{3496}`, `{3794,3795}`,
`{3800,3803}`, and `{3979,3865,4684}`. Each preserves exact membership iff,
exact cardinality, and a conditional radius map to B13. Source hashes: 376
`489bc408...31bc0b`, 375 `b3d1a776...b6a14d`, 373 `bd298881...32657`, 371
`00090f96...5f3a5`, 368 `24af95e5...f524e`. No certificate or id was paid.
All corresponding verifier and static checks pass; the chain remains **CI
pending** with no local Lean elaboration/olean.

## 2026-11-02 - parts 260-264 (387 -> 368, condensed)

Added the 387 bridge for `{37,3149}` (`97c1bbf2...14c34`), then `Refine375`
(`c2b0c5be...b877`), `Refine373` (`bd298881...32657`), `Refine371`
(`00090f96...5f3a5`), and `Refine368` (`24af95e5...f524e`). The removals were
`{3496}`, `{3794,3795}`, `{3800,3803}`, and `{3979,3865,4684}`. Each exact
membership/cardinality interface maps residual certificates to B13. Verifiers
and static checks pass; all remain **CI pending**, with no id paid.

## 2026-11-02 - parts 265-266 (368 -> 366 -> 364, condensed)

Added `Refine366` (`95a88c26...4c456`) removing green `{4650,4244}`, then
`Refine364` (`9430037f...67010`) removing green `{3778,4313}`; both exact
membership/cardinality interfaces map residual radius certificates to B13.
Audits `verify_census_366.py` and `verify_census_364.py` pass exact complement,
ordering, forbidden-token, `py_compile`, and `git diff --check` checks. Scope is
static/exact-set only, **CI pending**, and pays no id.

## 2026-11-02 - part 267 (364 -> 362 via green 3522/3783)

Added `Refine362` (`d8f6135b...11a5885`), removing CI-green `{3522,3783}` from
364 with exact membership iff/cardinality and a conditional radius map to B13.
`verify_census_362.py` (`c7cd2a2d...77cf0ac`) passes exact complement, ordering,
and static checks; 182 unique targets. **CI pending**, no payment.

## 2026-11-02 - part 268 (362 -> 360 via green 3808/3821)

Added deterministic `emit_census_360.py` and emitted
`EnergyTerminalResidualCensusRefine360.lean` (SHA256
`0018226b8e2c53476a9cc98c147a9e58fccd47c4b4200a97ebb17b04dd5748c8`).
It imports pending `Refine362` plus CI-green `Refine3808`/`Refine3821`,
proves both ids are in the 362 set, removes them exactly, gives cardinality 360,
and maps 360 residual certificates to `EnergyTerminalBatchB13.RemainingTerminalRadius`.
No id is paid. `verify_census_360.py`
(`e1f1d0643b828b35cc70d21991deda57c9dc2ca491a87072a74e08ef407aaddb`)
passes exact 389->360 complement (29 removals), dependency ordering,
`py_compile`, forbidden-declaration scan, and `git diff --check`; 183 unique targets.

The first emitted scan exposed a wrong parent theorem suffix; it is corrected and
asserted by the verifier. Scope is static/exact-set only: **CI pending**, with no
project elaboration/olean or kernel credit. Still unproved: elaboration of the
360 chain, 360 radius certificates, 327 source-missing ids, SevenClassExclusions,
and the arbitrary-centre theorem. Next: CI-build 360 after 362; if green, bridge
360 -> 358 with unused green `3851`/`4162`; if red repair the first error.

## 2026-11-02 - part 270 (358 -> 356 via green 2965/3040)

Added deterministic `emit_census_356.py` (SHA256 `e8798ee5...9b1d`) and emitted
`EnergyTerminalResidualCensusRefine356.lean` (SHA256
`c6c487b274e5be7b2d4847e618ee342e0c5c41bf99c66a92160632ccaac90810`).
It imports pending `Refine358` plus CI-green `EnergyTerminalBatchB13Refine2965`
and `Refine3040` (batch and Main exits are both 0 in run `41378003343`). It
proves both ids are in the 358 set, removes them exactly, gives cardinality 356,
and maps 356 residual certificates to
`EnergyTerminalBatchB13.RemainingTerminalRadius`. No id is paid.
`verify_census_356.py` (SHA256 `6cd79e68...5dc0`) passes exact membership and
389 -> 356 complement (33 removals), dependency/target ordering, `py_compile`,
forbidden-declaration scan, and `git diff --check`; 185 unique targets.

Scope is static/exact-set only: **CI pending**, with no project elaboration/olean
or kernel credit. Still unproved: elaboration of the 356 chain, 356 radius
certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build 358 then 356; if green, 356 -> 354 with
unused green `3440`/`3520`; if red repair the first error.

## 2026-11-02 - part 269 (360 -> 358 via green 3851/4162)

Added deterministic `emit_census_358.py` (SHA256 `147940a1...0eb2`) and emitted
`EnergyTerminalResidualCensusRefine358.lean` (SHA256
`de71b9a6667f5cb1a99c2b07b0716487cc3754516acc328b3edb0b749a0f0d44`).
It imports pending `Refine360` plus CI-green `EnergyTerminalBatchB13Refine3851`
and `Refine4162` (all six singleton/batch/main entries exit 0 in run `41378003343`).
It proves both ids are in the 360 set, removes them exactly, gives cardinality
358, and maps 358 residual certificates to
`EnergyTerminalBatchB13.RemainingTerminalRadius`. No id is paid. `verify_census_358.py`
(SHA256 `aa8afd00...2b59e`) passes exact census membership and 389 -> 358
complement (31 removals), dependency/target ordering, `py_compile`,
forbidden-declaration scan, and `git diff --check`; 184 unique targets.

Scope is static/exact-set only: **CI pending**, with no project elaboration/olean
or kernel credit. Still unproved: elaboration of the 358 chain, 358 radius
certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build 360 then 358 in order; if green, use
unused fully-green tuples (candidates 2965, 3040, 3440, 3520, 3589, 3623, 3802,
3807, 3810, 3863) for a 358 -> 356 bridge; if red repair the first error.

## 2026-11-02 - part 271 (356 -> 354 via green 3440/3520)

Added deterministic `emit_census_354.py` (SHA256
`694f7fafa7d6ce84aa47fa86240921dc45d01ee5a68fb3c9967d37272cb73e24`) and
emitted `EnergyTerminalResidualCensusRefine354.lean` (SHA256
`f03822bdc0f121ee0489dc3080cdd5d3c39be5d59d85472bcb5cbed0eb76a821`).
It imports pending `Refine356` plus CI-green `EnergyTerminalBatchB13Refine3440`
and `Refine3520` (singleton and Main exits 0 in run `41378003343`). It proves
both ids are in the 356 set, removes them exactly, gives cardinality 354, and
maps 354 residual certificates to
`EnergyTerminalBatchB13.RemainingTerminalRadius`. No id is paid.
`verify_census_354.py` (SHA256
`a660c02f96f2871da10e5977bea4670ded17d97a0b075a30903b0c94a1ef7361`)
passes exact membership and 389 -> 354 complement (35 removals),
dependency/target ordering, `py_compile`, forbidden-declaration scan, and
`git diff --check`; 186 unique targets.

Scope is static/exact-set only: **CI pending**, with no project elaboration/olean
or kernel credit. Still unproved: elaboration of the 354 chain, 354 radius
certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build 356 then 354; if green, extend
354 -> 352 with fully-green `3589`/`3623`; if red repair the first error.

## 2026-11-02 - part 272 (354 -> 352 via green 3589/3623)

Added `emit_census_352.py` (SHA256
`95050edee06b06d03888d6064a5005babaadd6096068853e1cdcffff70791417`) and
emitted `EnergyTerminalResidualCensusRefine352.lean` (SHA256
`41297a5c9755de630db056b20d0665f06d47c28d5cb5c069f346413ac84edcca`).
It imports pending `Refine354` plus CI-green `EnergyTerminalBatchB13Refine3589`
and `Refine3623`, proves both ids are present, removes them exactly, gives
cardinality 352, and maps 352 residual certificates to B13. No id is paid.
`verify_census_352.py` (SHA256
`31042241dcf2e6bbd7f0b241b8fa6df33074afebb78feca2c19100366b33ccda`)
passes exact membership, the 389 -> 352 complement (37 removals), dependency
and unique-target ordering, `py_compile`, forbidden-token scan, and
`git diff --check`; 187 unique targets. Scope is static/exact-set only:
**CI pending**, no project elaboration/olean or kernel credit. Next: CI-build
354 then 352; if green extend to 350 with green `3802`/`3807`; if red repair
the first error. Still unproved: all 352 radius certificates, 327
source-missing ids, SevenClassExclusions, and the arbitrary-centre theorem.

## 2026-11-02 - part 273 (352 -> 350 via green 3802/3807)

Added `emit_census_350.py` (SHA256 `e61d26ab...23ea`) and emitted
`EnergyTerminalResidualCensusRefine350.lean` (SHA256
`8c43d82e1894c491a1d95405313d7caaef8708c2b5c00d14522744635c873083`).
It imports pending `Refine352` plus CI-green batches `Refine3802` and `Refine3807`,
proves both ids are in the 352 residual set, removes them exactly, proves
cardinality 350, and maps 350 residual certificates to B13. No id is paid.

`verify_census_350.py` (SHA256 `845a1be6...da615`) passes the exact 389 -> 350
complement audit (39 removals), membership/cardinality source assertions,
dependency and unique-target ordering, `py_compile`, forbidden-declaration scan,
and `git diff --check`. Scope is static/exact-set only: **CI pending**, with no
project elaboration/olean or kernel credit. Still unproved: elaboration of the
pending 350 chain, all 350 radius certificates, 327 source-missing ids,
SevenClassExclusions, and the arbitrary-centre theorem. Next: CI-build 352 then
350; if green, extend with two unused fully-green refinement ids; if red, repair
the first Lean error and preserve its log.

## 2026-11-02 - part 274 (350 -> 348 via green 3810/3863)

Added `emit_census_348.py` (SHA256 `c03c8da2788df78d2a5dd0e66de8161f1a9d190c73bef06b761420d217ae04c9`)
and emitted `EnergyTerminalResidualCensusRefine348.lean` (SHA256
`f9b4c0d06a8dbdbea2cea5c4176a9f61af2a30592424e47491a82d57260d69d5`).
It imports pending `Refine350` plus CI-green `EnergyTerminalBatchB13Refine3810`
and `Refine3863`, proves both ids are present, removes them exactly, proves
cardinality 348, and maps 348 residual certificates to B13. No id is paid.
`verify_census_348.py` (SHA256 `b615bc6fdf28dc2ee3c95ac36bc5908ac15758e829469b62e452a421fc395cba`)
passes the exact 389 -> 348 complement audit (41 removals), membership and
cardinality assertions, dependency/unique-target ordering, `py_compile`,
forbidden-declaration scan, and `git diff --check`; 188 unique targets.
Scope is static/exact-set only: **CI pending**, with no project elaboration/olean
or kernel credit. Still unproved: elaboration of the 348 chain, all 348 radius
certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build 350 then 348. No unused fully-green
numeric `EnergyTerminalBatchB13RefineNNNN` pair remains in run `41378003343`
(the only unmatched numeric names are `0039`/`0040`, whose builds are red), so if
green the next step is to inspect residual certified-source modules rather than
draft another set-reduction bridge; if red repair the first Lean error.
