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

CI `41318867156` OOM-killed four census parts; they became serial
`C01 -> C02 -> C03 -> C04` (resource repair, not a theorem), **CI pending**.

## 2026-11-01 - parts 247-248 (N39 restoration and scheduling)

Restored archive id 39 (K=13; archive `959ec36e...5ae2`, restored
`5bbe2fdb...a3d`), dropping only its unbounded heartbeat directive. Wrapper/main
were conditional and **CI pending**; no id paid.

## 2026-11-02 - parts 249-252 (N39 repair; structural census start, condensed)

Generated `EnergyRefineN0039Repair.lean` (`42cf57bf...fe472d`), replacing only the
timing-out `pk_ok` tactic. Census work moved to structural membership/cardinality
proofs. No id paid; checks were static/exact-set only and **CI pending**.

## 2026-11-02 - parts 253-272 (389 -> 358, condensed)

Structural/conditional bridges cut 389 to 358 via 368, 364, 360 and 358, using
the archived token-clean refinements listed in `TARGETS.txt`. Exact membership
iff, cardinality, ordering, forbidden-token and complement checks passed. Scope
is static/exact-set only; **CI pending**, no id paid.

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

`emit_census_348.py` and `EnergyTerminalResidualCensusRefine348.lean` remove the
green 3810/3863 ids exactly (card 348, conditional B13 map, no payment).
`verify_census_348.py` passed the 389 -> 348 complement and ordering checks.
Scope: static only, **CI pending**.

## 2026-11-02 - parts 275-277 (low-id repair; 348 -> 346; chain audit)

CI job `125106045871` exposed the original 39 repair errors at
`EnergyRefineN0039Repair.lean:51-53,57-59` (`False` returned for conjunction
goals, hence `sorryAx`). `EnergyRefineN40` itself was green, but its batch used
the module name `EnergyRefineN40` instead of namespace `EnergyRefineN0040` and
misused upper bound `next505_lt` for low ids 39/40.

`repair_refine_0039_40.py` (`ef1dfa56...8ac76`) regenerated
`EnergyRefineN0039Repair.lean` (`d36d4491...cb5a`), `Refine0039`
(`914fe9bd...f158`), and `Refine40` (`86bcbe3c...dfd5`): `False.elim` covers the
six false leaves, both batches prove Next505 nonmembership by 25 literal blocks,
and N40 uses namespace `N0040`. `emit_census_346.py` (`9c88d3d8...08c1`) emitted
`EnergyTerminalResidualCensusRefine346.lean` (`ea12788b...4545a`), removing 39/40
with exact membership iff, card 346, and the conditional B13 map. No id paid.

`repair_census_membership_chains.py` (`9e504abf...942f`) found skipped parent
subtractions in every pending `Refine348..362` membership proof and normalised
the two blocks in each to the contiguous `RefineTriple` suffix. `verify_census_346.py`
(`bfa2fba8...3536`) now checks exact 389 -> 346 complement, forbidden tokens in
all nine pending modules, TARGETS ordering, `py_compile`, and all nine rewrite
chains. Run result: `{"census_count":389,"membership_chains":"9 checked",
"refined_count":346,"removed_count":43,"static_checks":"PASS"}`; `git diff
--check` passes. Scope is source/static/exact-set only, not elaboration or
kernel credit. CI run `41380560959` remains in progress; later runs used only
scoped replay, not `n11-lean-build`.

Still unproved: CI elaboration of repaired 39/40 and the 346 chain, all 346
radius certificates, 327 source-missing ids, canonical packet production,
SevenClassExclusions, and the arbitrary-centre full-disk theorem. Next: when CI
reaches `EnergyRefineN0039Repair`, require zero errors/`sorryAx`; then build 346
serially and repair the first reported declaration. If green, consume the 346
B13 map and resume exact residual radius work.

## 2026-11-02 - parts 278-279 (chain/exception audit)

`verify_census_346.py` PASS at SHA `ea12788b...4545a` (389/43/346/nine chains).
The exceptional `b13_remaining_of_residual346` branches were checked against the
two `.new_radius` results and their `.le` conversions. Scope stayed source/static
only; no elaboration, kernel credit, or paid id.

## 2026-11-02 - parts 280-282 (CI log boundary; 346 -> 344)

Run `41380560959`, job `125106045871`, remained `in_progress`; the 729 MB live
log was only partially retrievable to 06:35 UTC, with clean axiom reports before
the frontier and no repairable error line. Scope: partial CI-log retrieval only.

Restored unused residual archive refinements 3825/3854 verbatim from
`origin/ci/n11-build`, removing exactly one `set_option maxHeartbeats 0` in each.
SHA256: `EnergyRefineN3825.lean` `e2e9831a...b237b`, `EnergyRefineN3854.lean`
`dd834d8f...37ba7c`. Generated B13 wrapper/main pairs for both from the reviewed
3853 template, then emitted `EnergyTerminalResidualCensusRefine344.lean`
(`0b2b3e4c...003e1`): exact removal of `{3825,3854}` from 346, cardinality 344,
membership iff, and `b13_remaining_of_residual344`. No id is paid.

`emit_census_344.py` (`28ee04cc...33f48`) and `verify_census_344.py`
(`164a0a6b...ec41f`) pass: 389 -> 344 complement (45 removals), exact archive
bytes after the one-line removal, forbidden-token scan, both rewrite chains,
dependency/TARGETS ordering, `py_compile`, and `git diff --check`. Regression
`verify_census_346.py` and the nine-chain audit also pass. Scope is
source/static/exact-set only: **CI pending**, no project elaboration/olean or
kernel credit.

Still unproved: elaboration of 346 and the new 344 chain, all 344 radius
certificates, 327 source-missing ids, canonical packet production,
SevenClassExclusions, and the arbitrary-centre theorem. Next: CI-build 346, then
3825/3854 batches, then 344; repair the first reported declaration. If green,
bridge 344 -> 342 only from another unused token-clean residual source.

## 2026-11-02 - parts 283-284 (344 -> 342 via archive drafts 3490/3517)

Added `emit_census_342.py` and emitted `EnergyTerminalResidualCensusRefine342.lean`
(SHA256 `9dc0254e5526d7502c7f1188841d0b71eac33a034196b92908e1de27ee289bf8`).
Restored archive drafts `EnergyRefineN3490.lean` (`515b48fe...877b`) and
`EnergyRefineN3517.lean` (`f7a9a0bd...7856`) verbatim except for deleting one
forbidden `set_option maxHeartbeats 0`; generated their singleton B13
wrapper/Main triples from the 3853 template. The 342 module imports Refine344,
proves both ids remain in the 344 residual set, removes them exactly, proves
cardinality 342, and gives `b13_remaining_of_residual342`. No id is paid: these
archive sources are exact-rational pre-validated drafts marked NOT compiled.

`verify_census_342.py` PASS: 389 census hash, exact 47-removal complement to
342, restored bytes after the one-line directive removal, both wrapper triples,
forbidden-token scan, dependency/target ordering, membership chains, and
`py_compile`. Regression `verify_census_344.py` PASS (389/45/344); the shared
chain auditor now includes 342/344 and its old nine-module sweep still PASSes.
Scope is source/static/exact-set only: **CI pending**, no project elaboration,
olean, kernel credit, or rational-payload recheck.

Still unproved: elaboration of 346 through 342, all 342 radius certificates,
3490/3517 draft validation, 327 source-missing ids, canonical packet production,
SevenClassExclusions, and the arbitrary-centre theorem. Next: CI-build 344,
then 3490/3517 triples, then 342; require exit 0 and axiom report
`[propext, Classical.choice, Quot.sound]`, repairing the first error otherwise.

## 2026-11-02 - parts 285-287 (342 -> 340; bridge inventory)

Added `emit_census_340.py` and `EnergyTerminalResidualCensusRefine340.lean`
(`2660f538...12b3`, card 340), restoring drafts 3432/3550 verbatim except one
unbounded-heartbeat directive. `verify_census_340.py` PASS covered the exact
389 -> 340 complement, bytes, tokens, ordering, chains, and `py_compile`.
`audit_residual_bridge_inventory.py` then checked all 49 prior removals are
absent from the 340 residual (`residual-bridge-inventory.json`). Scope was
source/static/file inventory only; **CI pending**, no id paid.

## 2026-11-02 - part 288 (340 -> 338 via archive drafts 38/3781)

Added `emit_census_338.py` (`ed2b9c71...533d9`) and emitted
`EnergyTerminalResidualCensusRefine338.lean` (`6fa6faf1...72ea9`). Restored the
two smallest remaining archive refinements: `EnergyRefineN0038.lean`
(`aa4049ec...0df95`) and `EnergyRefineN3781.lean`
(`1d5020b4...ae6bfb`), verbatim except for deleting `maxHeartbeats 0`; generated
their conditional wrapper/Main triples. The bridge proves both ids remain in the
340 residual set, removes them exactly, proves cardinality 338, and maps 338
radius certificates to B13. No id is paid.

`verify_census_338.py` (`7298c851...1d12b`) PASS: exact 389 -> 338 complement
(51 removals), restored-byte hashes, forbidden-token scan, wrapper/Main shape,
dependency/TARGETS ordering, membership chain, `py_compile`, and `git diff
--check`. Scope is source/static/exact-set only: **CI pending**, no project
elaboration/olean or kernel credit, and no exact-rational payload recheck.

Still unproved: CI elaboration through 338, all 338 radius certificates,
38/3781 draft validation, six unused archive drafts (3/23/3564/3569/3578/3738),
327 source-missing ids, canonical packet production, SevenClassExclusions, and
the arbitrary-centre theorem. Next: CI-build 338; if green repeat the same
byte-checked bridge with the next two unused archive drafts (3564/3569).

## 2026-11-02 - part 289 (338 -> 336 via archive drafts 3564/3569)

Added `emit_census_336.py` (`ffbd08ab...3ecd8`) and emitted
`EnergyTerminalResidualCensusRefine336.lean` (`51032cd8...00b3`). Restored
`EnergyRefineN3564.lean` (`04dbf5cc...93ea`) and `EnergyRefineN3569.lean`
(`5de5a87f...8400`) except the banned heartbeat directive; generated their
wrapper/Main triples. The bridge removes both ids exactly (card 336) and maps
336 certificates to B13. `verify_census_336.py` (`88c11d32...011b`) PASSed the
exact complement, bytes, token/shape/chain/order checks, but scope is static
only: **CI pending**, no elaboration/kernel credit or payload recheck. Remaining:
3564/3569 validation, 336 certificates, 3/23/3578/3738, 327 missing sources,
SevenClassExclusions. Next was CI-build 336, then 3578/3738.

## 2026-11-02 - part 290 (336 -> 334 via final archive drafts 3578/3738)

Added `emit_census_334.py` (`a9d87650...7ab8`) and emitted
`EnergyTerminalResidualCensusRefine334.lean` (`aa641575...6148`, card 334).
Restored `EnergyRefineN3578.lean` (`bd8a0e6a...8a26`, 236738 bytes) and
`EnergyRefineN3738.lean` (`16310141...1ee9`, 340997 bytes) byte-for-byte from
the CI archive after removing the banned unbounded-heartbeat directive; generated
their conditional wrapper/Main triples. The bridge proves both ids are in the
336 residual, removes them exactly, proves card 334, and maps 334 certificates
to B13. `TARGETS.txt` orders all seven modules after 336.

Static PASS: new hashes, `py_compile`, forbidden-token scan across seven files,
338->336 parent import, card/name checks, unique target and order. Scope is
source/static only: **CI pending**, no elaboration/olean/kernel credit or rational
payload recheck. Unproved remains: CI through 334, all 334 radius certificates,
3578/3738 draft validation, 327 source-missing ids, SevenClassExclusions, and the
arbitrary-centre theorem. Next: CI-build 334; preserve the first error and repair
it if red, otherwise audit the remaining archive-draft inventory (drafts exhausted).
