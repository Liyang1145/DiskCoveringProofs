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

## 2026-11-02 - parts 253-264 (389 -> 368, condensed)

Structural bridges through `RefineTriple` (387), 385, 378, 377, 376, 375, 373,
371, and 368 remove ids `{37,3149}`, `{3112,3853}`, `{3116,3431,3573,3777,
2337,2341,3633}`, `{3841}`, `{3792}`, `{3496}`, `{3794,3795}`, `{3800,3803}`,
and `{3979,3865,4684}`. Each preserves exact membership iff, cardinality, and a
conditional radius map to B13. Verifiers/static checks pass; **CI pending**, no
id paid.

## 2026-11-02 - parts 265-266 (368 -> 366 -> 364, condensed)

Added `Refine366` (`95a88c26...4c456`) removing green `{4650,4244}`, then
`Refine364` (`9430037f...67010`) removing green `{3778,4313}`; both exact
membership/cardinality interfaces map residual radius certificates to B13.
Audits `verify_census_366.py` and `verify_census_364.py` pass exact complement,
ordering, forbidden-token, `py_compile`, and `git diff --check` checks. Scope is
static/exact-set only, **CI pending**, and pays no id.

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

## 2026-11-02 - parts 278-279 (chain/exception audits; CI inaccessible)

Re-ran `verify_census_346.py`: PASS, exact module SHA
`ea12788b26a0a6552c9f2f1007b8a70fa56b1755e7e2af2df1faddbe5a24545a`,
389 census / 43 removed / 346 refined / nine chains. Manually audited the two
exceptional branches of `b13_remaining_of_residual346` against
`EnergyRefineN0039.new_radius` and `EnergyRefineN0040.new_radius`: both produce
`sourceRadius < r`, and their `.le` conversion satisfies the `≤` goal. The
`newIDs` singleton membership arguments and the N40 namespace also match.

`gh` is absent and no local project oleans exist, so CI job `125106045871` and
run `41380560959` could not be inspected; scope remains source/static only, no
elaboration, kernel credit, or paid id. Still unproved: all 346 radius
certificates and the external premises. Next: with CI access, read the earliest
failure in `EnergyRefineN0039Repair` first; if green, build `Refine346` and run
its axiom checks.

## 2026-11-02 - part 280 (live CI log retrieval; still in progress)

Re-ran `verify_census_346.py`: PASS (`389` census, `43` removed, `346`
refined, nine repaired chains); module SHA remains
`ea12788b26a0a6552c9f2f1007b8a70fa56b1755e7e2af2df1faddbe5a24545a`.
GitHub API confirms run `41380560959`, job `125106045871`, remains
`in_progress` at its `Build` step (started 05:15 UTC); run `41399703011` has no
jobs. The live job log is 729,520,472 bytes; an 8-second ranged fetch returned
152,231,287 bytes but Azure ignored the requested suffix range, reaching only
06:35 UTC (`ActualNearestRingTriangles` / `ActualLocalSurfaceData` replay, all
shown axiom reports clean). No error line near the current build frontier was
available, so no repair is justified. Scope: exact-set verifier PASS and partial
CI-log retrieval only; no elaboration result or id paid.

Next: fetch the log's true suffix (or wait for completion), locate the earliest
`error:` after the 346 target, repair that declaration, then rerun
`verify_census_346.py`. Missing: elaboration/all 346 radius certificates, the
327 source-missing ids, SevenClassExclusions, and the arbitrary-centre theorem.
