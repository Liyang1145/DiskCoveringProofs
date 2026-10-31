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

## 2026-10-31 - parts 209-214 (condensed: Tree bridges, census, consumers)

- Five-field Tree bridges switched to definitional `rfl`; the pre-repair
  artifact had reddened both Tree modules. Repaired 373 census removed the
  erroneous `+revert` and trailing `norm_num`; `Census` SHA256 is
  `16ee97f14ff067f3f26195c2e7929473a4191d81e0bd244dc157510be71c846b`.
- Added literal-373 consumers `remaining_of_residual373_radius_certificates`
  and `b13_remaining_of_residual373_radius_certificates`, plus
  `EnergyTerminalBatchB13RefineSixteenResidualCensusMain` with four endpoints.
  These compose premises; they pay no id. `CensusMain` SHA256 is
  `569fb93edf013085d33caf10981a012a1c8c2c0eb8de9afb76f9b3d73e68b268`.
- Exact <5-field host search found no rescue for the seven public records.
  Public audit still finds 7 payloads and 382 absent payloads. Producer and
  radius certificate are proved equivalent, so packet production is not a
  weaker escape. Repaired Census/CensusMain have no post-repair CI artifact.

## 2026-10-31 - part 215 (nine archived split certificates restored; CI pending)

The prior archive audit found 57 refinement modules from
`origin/ci/n11-build` commit `8de79f774f8dcb1513855dfd54832bdfcce74e3f`;
27 were unused and token-clean. Restored the nine smallest such certificates
byte-for-byte into new `EnergyRefineN{3149,3496,3794,3795,3800,3803,3979,3865,4684}.lean`.
Generated the corresponding B13 and Main wrappers from the reviewed 3853
template. Each id is in the literal 373 census, each source defines the
singleton `newIDs`, and each source is free of `sorry`/`admit`/new `axiom`/
`native_decide`/`implemented_by`/`ofReduceBool`/`maxHeartbeats 0`.

Emitter (rerunnable): `n11-work/ops/lanes/C/restore_archive_refinements_batch2.py`.
Hashes: 3149 `ed34a561652a2ab6cd95ff4143822006710c3cfbcf3b915d52d60db14e5337b0`;
3496 `8194096c8e2a2a3752e673af96d7ee945a6570a84288d31f325a1097dafcd57e`;
3794 `26515e54dcaadb4a1e6267208bdf2093743a118e0e8040bb69bad33bb5b912c0`;
3795 `68b1b0776ce9c2d1d6ee2871a81decf7ee9022455b2dbd3825b0e1c9841a9604`;
3800 `56361b64f4bb581897e2abcc82bc928da9ce5358b5e69bdab36600667769110f`;
3803 `1094884a1e8de964a73aba4d3e137243d051a6b6aadcc26c89299c1f9c02e946`;
3979 `d5a330bd06564cbc58d345ea2ea18b7cced6e5a272f00a793d6927a6a4d02664`;
3865 `1b26f67d435be6166da850773cc401186bc6a73e3c7a11794b3358f5a7cee731`;
4684 `503576280739503ff8000af16ba0cb29fd8d13ba4f39c81e9760033dc81b17c7`.
Emitter `25687f2f9fc5826d5115fe4e5f824b00d6543fa69f1c5e4406e3810d17eefb3b`.

Added all 27 certificate/wrapper targets to `TARGETS.txt`, uniquely. Checks:
restore script exit 0, `git diff --check` exit 0, forbidden-token scan exit 1
(no matches), target uniqueness assertions pass. Scope is byte/static audit
only: all nine certificates and wrappers are **CI pending**, no id is newly
paid and no kernel result was obtained locally.

Still unproved: 373 minus any newly green certifications; the remaining archive
payloads, geometric producer, seven-class/energy premises, and root integration.
Very next step: inspect the next `n11-lean-build` `summary.json` for these nine
pairs and the repaired Census/CensusMain; retain only exit-0 results as paid.

## 2026-10-31 - part 216 (archive batch 3 restored; CI pending)

Restored nine further token-clean archived split certificates byte-for-byte
from `origin/ci/n11-build:ci-n11/drafts/energy/N11Formalization/`:
`EnergyRefineN{3778,4313,3810,4650,3520,3863,3807,40,3802}.lean`.  Emitted
matching `EnergyTerminalBatchB13RefineN*.lean` and `*Main.lean` wrappers from
the reviewed 3853 templates. Rerunnable emitter:
`n11-work/ops/lanes/C/restore_archive_refinements_batch3.py`; hash manifest:
`n11-work/ops/lanes/C/archive-refinements-batch3.json`.

Certificate SHA256 values (verbatim archive bytes):
3778 `8b07ae5bba9a6eb749019555abb65b7dc2834a148a4b3ac3e60adf6506a896cf`;
4313 `c5ce2fefde5eea14c2098807e4c6f2533938687d309377f303381e1c959c006c`;
3810 `135990494d4d403d2ae9bd95ca1657a425323516a91d8244adc0d602507a7785`;
4650 `bb31ca432a3cac588e16cab7e1779bb36cf8d63281af0c1ded0473ad209c10c3`;
3520 `36f844cc60a4d2fcc69dfa827df876e5c94bfba3ffe3b7c854e59001235dbab5`;
3863 `7c69880c79a3cb5fb05a56218dba907c233063612f3c78afb4cd417777d62e24`;
3807 `496377de7090bd70ad007d91f3b2585bc9a5154a2db9aff31cc3a7e8c22a7141`;
40 `bbb5ebf192558976f1685bf6966e2360e8f0fa9b15217af1e1c49d9f53ce1f00`;
3802 `193c1afdb9faee7ba42393a6cc73cebe1153b27a28bcdbf58826cca60866746a`.

Checks (scope: static/byte audit only, no local Lean build): emitter exit 0;
fresh `git show` byte comparisons all equal; forbidden-token scan exit 1 (no
matches); 27 unique targets appended, 139 unique total; `git diff --check`
exit 0. These nine certificates and 18 wrappers are **CI pending**, pay no id,
and supply no kernel credit. Eight clean archived certificates remain unused:
`{3522,3783,3808,3821,3841,3851,4162,4244}` (`0037` is already present).

Still unproved: all 373 residual radius ids unless CI greens these refinements;
the geometric producer, seven-class/energy premises, and root integration.
Very next step: when CI reports, retain only exit-0 batch-2/batch-3 modules and
then build one literal aggregate over the successfully compiled singleton ids
(a single B13 `paidIDs` union with exact disjointness and `remaining_of`), rather
than treating separate conditional wrappers as a paid residual count.

### CI observation for run 41222715534

Artifact `n11-build-41222715534` (head `8f861bae`, job "success") reports:
`FrozenCapFiveField2368`, `...2368Tree`, `...2370`, `...2370Tree` and
`FrozenCapRowCapTreeBridges` exit 0; **green**. The four residual-census modules
`EnergyTerminalResidualCensus`, `...RefineSixteen`,
`EnergyTerminalBatchB13RefineSixteenResidualCensus`, and the root exit 1. No
lane-C refinement certificate was in this commit: batch 2 and batch 3 remain
**CI pending**. The root failure visible in the artifact tail is unrelated
`SharedMomentConcreteSwitchBatch` OOM/code 137. Do not interpret the workflow's
overall "success" or the root failure as a verdict on a lane-C certificate.

## 2026-10-31 - part 217 (batch 4 restored; live CI manifest inspected)

Restored the final eight unused token-clean archived split certificates verbatim
from `origin/ci/n11-build` commit `8de79f77`: `EnergyRefineN{3522,3783,3808,3821,3841,3851,4162,4244}.lean`,
with 16 wrappers generated by `restore_archive_refinements_batch4.py`. This
completes the 26 previously unused archive certificates (0037 was already
present), but pays no id before CI. SHA256 values:
3522 `9c515ccb2fd21ead8a3977a27072224ec2b62f8c580490e19d18b0e65131dab0`;
3783 `7aa910eb6659df826cf6aac46ff88e3a1049a7be1359cc995953caf4fd436074`;
3808 `e147efc7f7269e123ff429dee17487a9b841c9ab58c02786d3d222b79ae9b672`;
3821 `0b7e4d8882fdb5ce0d9edf1fa64ad42f886198836115dbc89b0123e93551eb85`;
3841 `04bbc41a370d737e3c86508fcb6613057c3dc61354e5a7ea790eed8ac4a12c5c`;
3851 `2003b274e5a40069fa0a07f6cfb73032023e161b32c5ac656ccf2c306926aaf6`;
4162 `0f60192025e5bf0d20b3f9d3c708db0c1b523023167b98b57d87df11efd1fd34`;
4244 `b77a426c86253587281fa0bb5196b97b82808042db629a3a838af1b39914c22a`.

Checks (scope: static/byte audit only, no local Lean build): emitted certificates
compare byte-identically with fresh `git show`; emitter exit 0; forbidden-token
scan exit 1 (no matches); `git diff --check` exit 0; `TARGETS.txt` has 163 unique
targets. All batch-2/3/4 wrappers and certificates remain **CI pending**.

Live run `41222715534` (artifact `n11-build-41222715534`, head `8f861bae`)
reports `RefineSixteenRepair`, `RefineSixteenResidual`, `RefineSixteen`, and
`RefineSixteenMain` exit 0, but `RefineSixteenResidualCensus` exit 1 and the root
exit 1 from `SharedMomentConcreteSwitchBatch` OOM/code 137. None of the batch-2/3/4
modules is in this manifest. The repaired literal-373 census therefore remains
unpaid for kernel credit.

Still unproved: every residual radius certificate until its CI target exits 0;
the repair of `RefineSixteenResidualCensus`; a literal aggregate over the green
archive ids; packet production/canonicality, seven-class/energy premises, and
root integration. Very next step: fix the census failure from a targeted CI log
or have CI build the batch-2/3/4 targets; then emit one aggregate whose `paidIDs`
union contains only exit-0 singleton ids with explicit pairwise disjointness and
a `remaining_of` consumer.

## 2026-10-31 - part 218 (census failure diagnosed and repair drafted)

Downloaded public artifact `n11-build-41222715534` (head `8f861bae`) directly
from the GitHub artifacts API and read `summary.json.errors_head`. Exact census
failure: line 41 `No goals to be solved`; line 50 onward repeated `(kernel)
deep recursion detected` at every per-id `decide +kernel`, followed by
deterministic 200000-heartbeat `whnf` timeouts. This confirms the census did not
fail on a false residual id; it failed on the proof encoding.

Changed rerunnable emitter `emit_residual373_census.py` to emit scoped
`set_option maxRecDepth 10000`, prove `card_chunks` by one 373-literal
`decide +kernel`, and replace the 51 blocks' per-id decisions with
`simp [residual373, chunk0, chunk1, chunk2, chunk3]`. Regenerated
`EnergyTerminalBatchB13RefineSixteenResidualCensus.lean` (571 lines, SHA256
`8dbacbe8d48a07c6bc95d9d42dbe1e53bedc77f61f34fc8c408bbb8098d915a6`;
emitter `fee87cce3fb77febf2f412e8c63b05c52277a41cbf50e7c0b01f7a7c37d725dd`).

Checks (scope: exact CI-error extraction plus static emitter/byte checks only):
artifact download and JSON parse exit 0; emitter exit 0; forbidden-token scan
exit 1 (no matches); `git diff --check` exit 0. The repair is **CI pending**;
the census and both literal-373 consumers remain unpriced/conditional. Every
residual id is still unproved unless its own certificate target exits 0.
Next concrete step: inspect the next artifact's census result; if `simp` still
times out, split each block theorem into 10-id sub-blocks so no membership proof
unfolds all 373 literals at once. Then address batch-2/3/4 target visibility.
