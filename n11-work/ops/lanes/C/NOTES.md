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

## 2026-10-31 to 2026-11-01 - parts 202-234 (condensed)

Repaired residual modules and censuses were CI-green, but literal census aliases
and the structural 54-line variant remain **CI pending** and pay no id. Exact
inventory: 773 files / 53,178,301 bytes, seven known payload ids, 382 missing
(missing-set SHA256 `f09a5bc4...5e90`); the C450 archive has no packet schema.
`PaidCellCertificateMCap` fixes the mixture through `hf0`/`hg`, not all `beta`.
After repairing the `sum beta = 1` row and omitted `endpoint_lo(g)` factors, the
seven public ids' best float regions have exact-negative vertex gaps (closest
2356, `-7.388363184123934e-07`); this is region-local arithmetic, not payment.
Checks were exit 0 with exact rechecks, `py_compile`, token scans, and
`git diff --check`. No host-storage/kernel credit or residual id is claimed.

## 2026-11-01 - parts 235-244 (public seven thresholds, condensed)

All seven public residual proposal records now have exact 512/512-region
normalized-Farkas threshold coverage, independently replayed from proposal/DBM
rows. Each region excludes this fixed model's `lower > T2`; this is not global
infeasibility, kernel credit, a residual-id payment, or the arbitrary-centre
theorem. Reports and replay hashes remain in this directory; part 242 also
repaired an omitted weighted-sum row and endpoint factors. No new Lean target.

## 2026-11-01 - part 245 (residual source coverage, not the unavailable HOST taxonomy)

Added `audit_residual_payload_sources.py` and ran it over all 389 residual ids.
It classifies static source completeness from the exact census, the public
seven-record proposal, `DBMSourceTreeData`, and `origin/ci/n11-build` archive
modules. Result: 7 proposal-complete, 389 DBM-complete, 57 archive modules with
the full terminal/new_radius/newIDs/pk_ok shape, 42 of those 57 also free of
forbidden tokens, and 62 ids with any complete source (proposal ∩ archive = 2).
Thus 327 residual ids have neither a complete public proposal nor an archive
module; this supersedes the looser "382 absent payloads" wording for source
coverage. The historical 354-method-failure/35-zero-dual taxonomy is **not in
the public tree**, so no id was retroactively assigned to it.

The seven proposal ids already have 512/512 exact region-local threshold-Farkas
reports. The archive modules remain static drafts: no arithmetic replay or
kernel credit here. Existing `EnergyRefineN0037` is unchanged, hash
`7a0137826c2ea9c5975ee9d3b19952e409e86551b93262778933c3752240d0ac`, and was
already in `TARGETS.txt`; no new Lean target was added this part.

Files/hashes: audit script SHA256
`834d5a7850d398fe2fc1872e5c79a00b96cd7de98a8cd7ae1ad6776fc8407fe1`;
report `residual-payload-source-coverage.json` SHA256
`ddee740bd077e20c9b8879277991567301ce2c3e7eb3fe3dd5be4b602995e03f`.
Checks: `py_compile` exit 0; bounded audit exit 0; `git diff --check` clean.
The detector source necessarily contains the forbidden-token regex literals;
the generated report contains none.

Still unproved: arithmetic validity/kernel credit for all 57 archive drafts,
327 source-missing ids, SevenClassExclusions (0/7), and the arbitrary-centre
theorem. Next concrete step: obtain the first failing target from CI run
`41301935749` and repair the earliest clean archive module (`0037` is already
queued); do not batch more uncompiled drafts before identifying that failure.

## 2026-11-01 - part 246 (serialize residual census; CI OOM diagnosis)

Downloaded complete job log `124884637589` from CI run `41318867156`; the first
four lane targets were green (including `Refine0037`). `RefineSixteenResidualCensus` then launched
`EnergyTerminalResidualCensusC01` through `C04` concurrently; each reached
roughly 7.3-8.6 GB RSS and the OOM guard killed all four at 866 MB available
(exit 137). This is a resource failure, not a disproved census theorem.

Changed only the imports of the three formerly independent parts so the DAG is
`C01 -> C02 -> C03 -> C04`: `EnergyTerminalResidualCensusC02.lean` now imports
`C01`, `C03` imports `C02`, and `C04` imports `C03`; header comments state why.
C01 and all proof bodies are byte-unchanged. New hashes: C02
`abb36c8059a7d82cf57902854d88b820eb5c373cec43283796f6abd47ec46c49`, C03
`4e53cd56dd018820dd80baabcff81ecb5be4d6184b496d96a653879a2c712af7`, C04
`2981d3c2bc2d4b8c5687691013a758174f19091114ff15355a506a9f211ddd64`.

The prior uncommitted source audit is retained with its recorded hashes. Checks:
import DAG is the exact four-link chain; forbidden-token scan of C02-C04 and
`git diff --check` were clean. Scope is static scheduling repair only: **CI
pending**, no Lean module was kernel-checked locally and no residual id is paid.

Still unproved: census CI success, 373 radius certificates, 327 source-missing
ids, SevenClassExclusions (0/7), and the arbitrary-centre theorem. Next: CI-run
the queued census target; if memory is still excessive, split each 100-index
equivalence theorem again rather than adding targets.

## 2026-11-01 - part 247 (first formerly blocked archive refinement: id 39)

The source audit's 15 "forbidden" archive modules are not axiomatized drafts:
the detector matched `#print axioms` (plural is harmless) and an unbounded
`set_option maxHeartbeats 0`. Restored the smallest complete draft, id 39
(K=13), after removing exactly that one directive. Archive source SHA256
`959ec36e08213c58569167a4f6cca528e2e3c8ab4ff2bc4b0f58bf60a8cb5ae2`;
new `EnergyRefineN0039.lean` SHA256
`5bbe2fdb17bff213685e3eab77e0ee35267aa2b54a8e0a8fc914599f45f29a3d`.
Extended `restore_archive_energy_refine.py` with an explicit, count-checked
`--drop-unbounded-heartbeats` mode; SHA256
`66fb6792f82865ce13a6f6510f849818336fb849e1e46b8347255e3c6fbab948`.

Emitted conditional singleton consumers from the CI-green 2965 wrapper
template, changing only the id/namespaces: `EnergyTerminalBatchB13Refine0039`
extends B13 to 1998 ids, and `...Refine0039Main` weakens the existing seven-class
main consumer. Hashes `407b62f6...a6090` and `cfb72df3...f8f1b`; emitter
`emit_refine_singleton.py` is `4bbecb99...9e32`. Added all three module targets.

Checks: `py_compile` exit 0 for both lane emitters; generated-source key-shape
and stale-template scans clean; forbidden-token scan and `git diff --check`
clean. Scope is static generation only: **CI pending**, no local Lean build, no
new id is paid, and the 389-id census/main path is not yet rewired to N39.
Still unproved: N39 kernel success, arithmetic independence of its archived
packet, 327 source-missing ids, seven-class exclusions (0/7), and the
arbitrary-centre theorem. Next: obtain the CI verdict for the first N39 target;
if green, rebuild a 388-id census consumer excluding 39; if red, repair its
first exact elaboration failure rather than adding more drafts.
