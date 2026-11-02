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

## 2026-10-31/11-01 - parts 202-244 (condensed)

Repaired residual modules and censuses were CI-green; aliases stayed pending.
Inventory: 773 files, 7 public payloads, 382 missing (SHA `f09a5bc4...5e90`).
All seven public proposals have exact 512/512 threshold-Farkas coverage, but
best float regions have exact-negative gaps. Scope is region-local arithmetic.

## 2026-11-01 - part 245 (residual source coverage)

`audit_residual_payload_sources.py` classifies 389 ids: 62 have any complete
source, leaving 327 source-missing. The old 354/35 taxonomy is unavailable.
Report hash `ddee740b...e03f`; this is an audit, not kernel credit.

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

## 2026-11-02 - part 259 (376-id refinement interface)

Added `EnergyTerminalResidualCensusRefine376.lean` (SHA256
`489bc4081589094c6827042c1c1132e96d1cce7fcefc3c4660db2b812931bc0b`).
It imports pending `Refine377` and CI-green `EnergyTerminalBatchB13Refine3792`,
removes `{3792}`, proves its 377 membership from the archive terminal/radius
facts, gives exact cardinality 376 and membership iff, and bridges 376 residual
radius certificates to B13. It supplies no new certificate and pays no id.
Added as target 175; inventory is 175 entries / 175 unique.

Added `verify_census_376.py` (SHA256
`d1bd323e1545af14a4d41a02d12a99d97ae62f849293c27d8d7c771514c45a38`).
The exact 389 -> 376 set audit, `py_compile`, forbidden-token scan, and
`git diff --check` pass. No local Lean build/olean exists, so scope is static
source plus exact set arithmetic: **CI pending**; no elaboration, kernel credit,
MPacket validity, or payment claimed. `LATEST.md` predates this chain and still
reports the old N39 red and `SharedMomentConcreteSwitchBatch` OOM.

Still unproved: elaboration/kernel validity of the 376 chain, 376 residual radius
certificates, 327 source-missing ids, SevenClassExclusions (0/7), and the
arbitrary-centre theorem. Next: CI-build 378, 377, 376 in order; if green,
continue with another CI-green refinement bridge (for example 3149 or 3496);
if red, repair the first exact elaboration error without changing frozen bytes.

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
