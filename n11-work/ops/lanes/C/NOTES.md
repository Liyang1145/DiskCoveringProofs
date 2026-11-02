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

## 2026-11-02 - parts 249-252 (N39 repair and structural census start, condensed)

Restored archive id 39 (`5bbe2fdb...29a3d`) then generated
`EnergyRefineN0039Repair.lean` (`42cf57bf...fe472d`) with a deterministic emitter,
replacing only the timing-out backtracking `pk_ok` tactic. The conditional
singleton wrapper imports the repair. Kernel-scale residual census work was
changed to structural membership/cardinality proofs, avoiding large
`decide +kernel` unions. This paid no id; older N39 CI was red at heartbeat 200000.
All later checks in this section were static/exact-set only and CI pending.

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

## 2026-11-02 - part 260 (387-id bridge from green singletons)

Added `EnergyTerminalResidualCensusRefine0037Refine3149.lean` (SHA256
`97c1bbf2...14c34`), importing the CI-green singleton refinements for 37 and
3149. It proves both IDs lie in the 389 census, removes both, establishes exact
membership iff and cardinality 387, and maps 387 residual radius certificates
to `EnergyTerminalBatchB13.RemainingTerminalRadius` using the existing singleton
radii. It supplies no certificate and pays no id. The target is present before
the dependent triple bridge in `TARGETS.txt`.

Added `verify_census_0037_3149.py` (SHA256 `08ec22e5...307f0`). Its exact
389/387/386/385 set checks, `py_compile`, forbidden-token scan, and
`git diff --check` pass. Scope is static source and exact set arithmetic:
**CI pending**; no local Lean elaboration/olean, kernel credit, MPacket
validity, or payment is claimed.

Still unproved: the same 376/387 residual certificates and downstream
obligations. Next: CI-build this 387 bridge first; if green, continue with a
singleton bridge for 3496 (already CI-green archive tuple), otherwise repair
the first elaboration error without changing frozen bytes.

## 2026-11-02 - part 261 (376 -> 375 via green 3496)

Added `EnergyTerminalResidualCensusRefine375.lean` (SHA256
`c2b0c5bea8c8f5367602b5b395872314c64ba3c5969eba46ad80072e8780b877`), importing
pending `Refine376` and the CI-green `EnergyTerminalBatchB13Refine3496` tuple
(all three dependency targets show exit 0 in CI run `41352871085`). It proves
3496 lies in the 376 set, removes it, establishes exact membership iff and
cardinality 375, and maps 375 residual radius certificates to
`EnergyTerminalBatchB13.RemainingTerminalRadius` using the existing 3496
radius theorem. It supplies no new certificate and pays no id. Added as target
176, after both dependencies; inventory is 176 entries / 176 unique.

The membership proof unfolds all ancestor membership iff theorems explicitly,
then discharges the resulting conjunction with a bounded
`repeat' first | exact ... | decide | constructor` block. That tactic shape was
checked locally in core Lean on both opaque propositions and decidable Nat
inequalities.

Added `verify_census_375.py` (SHA256
`adcf7cc5bfd83415c7cfebb526e579204312a27c40c240944270b527d81de595`). Its exact
389 -> 375 complement, dependency/target ordering, `py_compile`, forbidden-token
scan, and `git diff --check` pass. Scope is static source plus exact set
arithmetic: **CI pending**; no project elaboration/olean, kernel credit, MPacket
validity, or payment is claimed.

Still unproved: elaboration/kernel validity of the 375 chain, 375 residual
radius certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build 375 after 376; if green, extend the
census with another already-green singleton (for example 3841 is already used
in the 377 bridge, so use 3794 or 3795) and if red repair the first elaboration
error without changing frozen bytes.

## 2026-11-02 - part 262 (375 -> 373 via green 3794/3795)

Added `EnergyTerminalResidualCensusRefine373.lean` (SHA256
`bd298881ebe0e6e7382deefd76dd612df78b6e3eab64ae0cb8ace7bc90b32657`), importing
the new 375 bridge plus CI-green `EnergyTerminalBatchB13Refine3794` and
`Refine3795` (all six singleton/refine/main entries exit 0 in run
`41352871085`). It proves both ids lie in the 375 set, removes them, gives exact
membership iff and cardinality 373, and maps 373 residual radius certificates
to B13 using the existing radius theorems. It supplies no new certificate and
pays no id. Added as target 177; inventory is 177 entries / 177 unique.

Added `verify_census_373.py` (SHA256
`abf4a1e5caad4c41dee921aba4c348a90e89399288e01e1730d8da57483d7b74`). Exact
389 -> 373 complement, target ordering, `py_compile`, forbidden-token scan, and
`git diff --check` pass. Scope is static source plus exact set arithmetic:
**CI pending**; no project elaboration/olean, kernel credit, MPacket validity,
or payment is claimed.

Still unproved: elaboration/kernel validity of the 375/373 chain, 373 residual
radius certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build in order 375 then 373; if green, fold
in 3800/3803 (next green singleton tuples) with the same structural pattern.

## 2026-11-02 - part 263 (373 -> 371 via green 3800/3803)

Added `EnergyTerminalResidualCensusRefine371.lean` (SHA256
`00090f964d5162ec2ce99aa31457b82c6bb8927f371e229e92d1c3f1efb5f3a5`), importing
pending `Refine373` and CI-green `EnergyTerminalBatchB13Refine3800` and
`Refine3803` (all six singleton/refine/main entries exit 0 in run
`41352871085`). It proves both ids lie in the 373 set, removes them, gives exact
membership iff and cardinality 371, and maps 371 residual radius certificates
to `EnergyTerminalBatchB13.RemainingTerminalRadius` using the existing radius
theorems. It supplies no new certificate and pays no id. Added as target 178;
inventory is 178 entries / 178 unique.

Added `verify_census_371.py` (SHA256
`4d7387d17f62d676170aa9df0c93bfcadac936e9016a222eb6d12ebb411a1a91`). Its exact
389 -> 371 complement (18 removals), dependency/target ordering, `py_compile`,
forbidden-token scan, and `git diff --check` pass. Scope is static source plus
exact set arithmetic: **CI pending**; no project elaboration/olean, kernel
credit, MPacket validity, or payment is claimed.

Still unproved: elaboration/kernel validity of the 371 chain, 371 residual
radius certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build 371 after 373 in order; if green,
extend with the next green archive singleton tuples (3979/3865/4684 appear
green in the same CI summary), otherwise repair the first elaboration error
without changing frozen bytes.

## 2026-11-02 - part 264 (371 -> 368 via green 3979/3865/4684)

Added `EnergyTerminalResidualCensusRefine368.lean` (SHA256
`24af95e562b5465093abdd97773a3097e3999c33c5a58927c929df9dfa8f524e`),
importing pending `Refine371` and CI-green `EnergyTerminalBatchB13Refine3979`,
`Refine3865`, `Refine4684` (all nine singleton/B13/main entries exit 0 in run
`41352871085`). It proves all three ids lie in the 371 set, removes them, gives
exact membership iff and cardinality 368, and maps 368 residual radius
certificates to `EnergyTerminalBatchB13.RemainingTerminalRadius` using the
existing radius theorems. It supplies no new certificate and pays no id.
Added as target 179 at the end of `TARGETS.txt` (179 entries, 179 unique).

Added `verify_census_368.py` (SHA256
`4cc3e445db03ad8ddaa4a017f01b919091d66fea25fb42692a3422b9697bc69e`). Exact
389 -> 368 complement (21 removals), dependency/target ordering, `py_compile`,
forbidden-token scan, and `git diff --check` pass. Scope is static source plus
exact set arithmetic: **CI pending**; no project elaboration/olean, kernel
credit, MPacket validity, or payment is claimed.

Still unproved: elaboration/kernel validity of the 371/368 chain, 368 residual
radius certificates, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build in order 371 then 368; if green,
continue with further green archive singleton tuples and a 368 -> 366 bridge.

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
