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

## 2026-11-01 - part 245 (residual source coverage)

`audit_residual_payload_sources.py` classifies all 389 ids from the census,
proposal, DBM data, and archive drafts: 7 proposal-complete, 57 archive modules
with the full refinement shape, 42 token-clean, and 62 with any complete source.
Thus 327 ids have neither a complete public proposal nor archive module. The
historical 354/35 taxonomy is unavailable, so no id was retroactively assigned.
The seven proposal ids already have 512/512 exact region-local threshold-Farkas
reports; archive drafts have no arithmetic replay or kernel credit. Hash of the
report is `ddee740b...e03f`; checks were clean. Still unproved: archive validity,
327 source-missing ids, SevenClassExclusions, and the arbitrary-centre theorem.

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

## 2026-11-01 - parts 247-248 (N39 restoration and scheduling)

Restored archive id 39 (K=13), dropping only its unbounded heartbeat directive;
archive hash `959ec36e...5ae2`, restored `EnergyRefineN0039` hash
`5bbe2fdb17bff213685e3eab77e0ee35267aa2b54a8e0a8fc914599f45f29a3d`.
Conditional singleton wrapper/main hashes are `407b62f6...a6090` and
`cfb72df3...f8f1b`. Static checks were clean; target ordering placed this tuple
first, but this paid no id. Scope was **CI pending**, with archive validity,
327 source-missing ids, exclusions, and the arbitrary-centre theorem unproved.

## 2026-11-02 - part 249 (N39 CI-red diagnosis and structural repair)

Downloaded run `41352871085` job `124986627384` (artifact summary plus full log).
The run-level conclusion says success, but its summary has `built_count = 0` and
exit `1` for all three N39 targets, so it is **CI red** for this lane. The first
error is `EnergyRefineN0039.lean:48:0`, a deterministic whnf heartbeat timeout
in the monolithic `pk_ok` proof; line 52's unknown `pk_ok` is downstream fallout.

Preserved the restored source byte-for-byte at SHA256
`5bbe2fdb17bff213685e3eab77e0ee35267aa2b54a8e0a8fc914599f45f29a3d`.
Added deterministic emitter `emit_refine_n0039_repair.py` (SHA256
`1c89926b6be880d683835b64f7c6928a9c6cda3ac423f246522b182251787b9d`),
which requires that exact source hash and replaces only the backtracking `first`
tactic with 13 explicit `fin_cases` branches. Generated
`EnergyRefineN0039Repair.lean` SHA256
`42cf57bfac90d2c68f5b618fa68caa08c7c77965bfcb2e7eb7a8d4def7fe472d`;
all nodes and packet bytes are inherited unchanged. The existing conditional
singleton consumer now imports the repair (SHA256
`62307f1634931f86d456db76375f9e3b35aac35cc918930b725c0bcae12518b2`);
its main consumer is unchanged. `TARGETS.txt` swaps only
`EnergyRefineN0039` for the repair, still first in the serial order.

Checks: `py_compile` and emitter exit 0; a source diff shows only the `pk_ok`
body; exact integer tree audit passes 100 root-scale and 1,200 split entries
(report SHA256 `cd18673676318547cd0d85e103db8a2c6bd7e4826ba8228040548995ae7390fc`);
forbidden-token scan and `git diff --check` are clean; target inventory is
167/167 unique. Scope is static repair plus exact integer tree data only:
**CI pending**, no local Lean build, packet validity, kernel credit or residual
id payment claimed. The earlier uncommitted fresh audit remains at
`energy-refine-n0039-fresh-tree-audit.json`, SHA256
`76d7de906e96abe61baa675851449681966755583f75cd1598e292b3a86c7bdc`.

Still unproved: repaired N39 elaboration/kernel validity, MPacket validity,
373 radius certificates, 327 source-missing ids, SevenClassExclusions (0/7),
and the arbitrary-centre theorem. Next: obtain the CI exit and axiom report for
`N11Formalization.EnergyRefineN0039Repair`; if green, check the two singleton
consumers, otherwise repair the new first exact error rather than raising the
heartbeat cap.

## 2026-11-02 - part 250 (N39 proof made definitional at the timeout)

Strengthened the deterministic N39 repair: the five false-terminal branches of
`pk_ok` now close by definitional reduction through core
`Bool.false_ne_true hl`, instead of invoking `decide +kernel`. The remaining
eight branches use the already-declared `valid3/4/5/9/10/11/12` theorems and
rfl equalities. This removes every decision procedure from the theorem that
timed out in CI. Updated only emitter `emit_refine_n0039_repair.py` and
regenerated `EnergyRefineN0039Repair.lean`; the archived source remains exactly
`5bbe2fdb17bff213685e3eab77e0ee35267aa2b54a8e0a8fc914599f45f29a3d`.

New emitter SHA256 `fe6b124ec040cdaaed3cd8455581594ced9de09e0cc2beffd15f935c6224d872`;
repaired source SHA256
`77dde91f17e1f686a0576587592893eee2669e4af8b1f2ff13eb4185b5c61290`.
The singleton consumer still imports the repair and is unchanged at
`62307f1634931f86d456db76375f9e3b35aac35cc918930b725c0bcae12518b2`.

Checks: emitter run and `py_compile` exit 0; target inventory 167/167 unique
with the N39 tuple first; forbidden-token scan clean; `git diff --check` clean.
A bounded local `Bool.false_ne_true` probe did not return under shared sandbox
load and has no verdict. Scope is static source repair only: **CI pending**;
no local Lean build, kernel credit, MPacket validity, or id-39 payment claimed.

Still unproved: repair elaboration/kernel validity and axiom report, MPacket
validity, 373 residual radius certificates, 327 source-missing ids,
SevenClassExclusions (0/7), and the arbitrary-centre theorem. Next: obtain CI
for `EnergyRefineN0039Repair`; if green, verify both singleton consumers and
then rebuild a 388-id residual census excluding 39; if red, repair the first
exact new failure without raising or removing the heartbeat cap.

## 2026-11-02 - part 251 (structural 388-id census interface)

Added `EnergyTerminalResidualCensusRefine0039.lean` (SHA256
`2914412baa79f28b243a48de27ba6740e10d62e3125a1ec2af5cb92fbec172eb`).
It defines the kernel-counted 389 census minus `{39}`, proves `39` lies in the
census from the repaired terminal fact, `not_paid_0039`, and a bounded
`decide +kernel` sharpness check, then proves the complement has cardinality
388. Its radius premise is connected by proof (not a new certificate) to
`EnergyTerminalBatchB13Refine0039.RemainingTerminalRadius` and hence B13. Source
39 is paid only conditionally on the still-unchecked N39 repair. Appended this
module as the fourth target; inventory is 168 entries / 168 unique.

Checks: Python emitter compile exit 0, target inventory and ordering assertion
exit 0, no forbidden declaration tokens in the new module (its two final lines
are allowed `#print axioms` diagnostics), `git diff --check` clean.
Scope: static Lean source plus structural census only; **CI pending**, no local
Lean build, kernel credit, radius certificate, or residual-id payment claimed.

Still unproved: N39 repair and 388-census elaboration/kernel validity, 388
radius certificates, 327 source-missing ids, SevenClassExclusions (0/7), and the
arbitrary-centre theorem. Next: obtain CI for the first four targets; if green,
replace the sixteen-based 373 interface with this 388 set and continue with the
next archive draft; if red, repair the first exact error without changing any
frozen bytes or heartbeat cap.

## 2026-11-02 - part 252 (structural N39 sharpness proof)

Replaced the 5011-literal `decide +kernel` proof that source `39` is absent
from `Patch120SharpDispatch.sharpIDs` with a structural argument in
`EnergyTerminalResidualCensusRefine0039.lean`: prove every explicit
`Patch120DomainPacket.patchID` value is at least 4436 by 120 bounded
`fin_cases`/`decide` branches, then contradict membership of `39`. Module
SHA256 is now
`a4a54083c2cf32066ae6d03829b0fa907b308cf043115d9cbf434dbb7df3851e`;
`TARGETS.txt` already lists it as the fourth target.

Checks: forbidden-declaration-token scan and `git diff --check` clean. A
bounded Mathlib probe of the membership/contradiction proof shape timed out
after 60 seconds under sandbox load and has no verdict. Scope is static source
hardening only: **CI pending**; no local Lean build, kernel credit, radius
certificate, or residual-id payment is claimed.

Still unproved: N39 repair and 388-census elaboration/kernel validity, 388
radius certificates, 327 source-missing ids, SevenClassExclusions (0/7), and
the arbitrary-centre theorem. Next: obtain CI for the first four targets,
starting with `EnergyRefineN0039Repair`; if green, wire the first valid
388-residual archive certificate into this census, otherwise fix the first
exact error without changing frozen bytes or the heartbeat cap.

## 2026-11-02 - part 253 (combined 387-id census interface)

Added `EnergyTerminalResidualCensusRefine0039Refine3149.lean` (SHA256
`870d5930b6349e4d7e0a7632143790afce64831cdf31ae8c94c42704290bfa57`).
It removes `{39,3149}` from the 389-id B13 census, proves a structural
120-row sharpness exclusion for 3149, gives the exact 387 cardinality and
membership characterization, and bridges 387 residual radius certificates to
B13 using the existing 39/3149 refinement radius witnesses. Added the module
as target 5 in `TARGETS.txt`. This supersedes the single-removal census as a
composable interface; the 388 module remains for diagnosis.

Checks: target inventory/inclusion, Python `py_compile`, forbidden-token scan,
and `git diff --check` exited 0. Scope is static Lean source only: **CI
pending**; no local build, kernel credit, MPacket validity, or payment of
39/3149 is claimed. Exact JSON membership recheck found both ids in the
389-element frozen census (count 389); the seven-class premise and all 387
radius certificates remain unpaid.

Still unproved: both census modules and N39 repair in CI, 387 residual radius
certificates, 327 source-missing ids, SevenClassExclusions (0/7), and the
arbitrary-centre theorem. Next: obtain CI for targets 1-5, especially
`EnergyRefineN0039Repair`; if green, wire a token-clean archive singleton into
the 387 census and extend to 386, otherwise repair the first exact error.
