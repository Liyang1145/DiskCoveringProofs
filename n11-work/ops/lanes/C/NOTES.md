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

## Condensed status through 2026-10-31 part 179

- Exact residual census remains 389 ids. Seven public exclusions
  `{1409,2337,2341,2356,2360,2368,2370}` are the only ones with public tree
  payloads; the other 382 remain absent from public evidence.
- Live run `41182882564`, source `7f7e6f3b`, proves the public row-cap path is
  kernel-green: smoke and all seven `FrozenCapRowCap*` modules exited 0. Scope:
  those module declarations only, not a packet/payment theorem.
- Same run: `FrozenCapFourFieldWitnesses`, five-field modules, public tree, and
  aggregate exited 1. Public tree was blocked by the syntax failure in
  `FrozenCapRowCapTreeBridges.lean:49`, not by its seven row-cap dependencies.
- Earlier conditional singleton/refinement payloads and B13 aggregates remain
  CI-green where `ci/LATEST.md` or the fresh run says exit 0. No root import was
  changed.
- Missing: exclusion-to-`RemainingTerminalRadius`; packet existence/`Valid`;
  382 residual payloads; MPacket validity; energy and seven-class premises.

## Condensed history through part 194

- Part 185: `FrozenCapFourFieldCorrectedRowCaps.lean` and
  `FrozenCapFourFieldCorrectedTree.lean` encode conditional exclusions for
  `1409`, `2337`, `2341`; exact row-cap checks passed, but payout remained open.
- Parts 189/190/191: exact five-field conditional exclusion chains were emitted
  for `2368` and `2370` (`FrozenCapFiveField2368*`, `FrozenCapFiveField2370*`),
  with 100 exact caps each and deterministic regeneration. They remain CI
  pending and pay no residual id. The old maximizing five-field report is
  invalid; the accepted criterion is strict `F0 + gain < T^2`.
- Parts 192-194: added `EnergyTerminalBatchB13ResidualCertificates.lean` with
  exact `ResidualRadiusCertificate`, `ResidualPacketProducer`, and canonical
  exclusion/producer interfaces plus real `RemainingTerminalRadius` consumers.
  Prior run `41193732877` predates this module; later run `41195990232` had not
  reached the lane-C target. Kernel status is therefore **CI pending**.
- Missing throughout: any residual radius/packet proof, 382 non-public payloads,
  canonical `f0Lo`/`g` identification, seven-class/energy premises, and root
  integration. No historical host-side exact audit is kernel credit.

## 2026-10-31 - part 195 (producer interfaces are exact radius obligations)

Extended `N11Formalization/EnergyTerminalBatchB13ResidualCertificates.lean`
with `residual_packet_producer_of_residual_radius_certificate`,
`residual_packet_producer_iff_residual_radius_certificate`, and
`canonical_packet_producer_iff_residual_radius_certificate`. The last theorem
takes `CanonicalPacketExclusion`; the forward direction uses that exclusion,
while the reverse direction uses the fact that a radius certificate makes the
strict counter-radius branch vacuous. Thus `ResidualPacketProducer n` is
exactly equivalent to `ResidualRadiusCertificate n`, and canonical production
under a frozen exclusion is likewise exactly the residual radius obligation.
This rules out treating packet existence as an independent, weaker shortcut.

Host checks: `git diff --check` exited 0; forbidden-token scan found no matches
in the module (the intentional `#print axioms` queries remain). Scope is static
Lean inspection only; the bounded Mathlib pattern probe did not finish before
the lane deadline. No local kernel claim. SHA256 (lowercase): module
`6e19343d207165d8f6a0675a09eb508c28524d57412d5299d2ea39b73d5c3e40`;
`TARGETS.txt` unchanged at
`692f6811aba3c1cb0c07d13ceb192df3340135f89cd57e8e587c33a7c6b5a1d3`.

Still unproved: the radius/packet obligation for every residual id, including
the seven public ids; all 382 absent payloads; canonical `f0Lo`/`g`
identification; seven-class and energy premises; root integration. The lane is
mathematically blocked on the residual radius theorem itself, not on a Lean
interface. Very next concrete step: read CI for
`EnergyTerminalBatchB13ResidualCertificates`; if red, fix its first failing
declaration, and if green, preserve the equivalences and redirect work to an
actual residual-radius proof source rather than more packet/row-cap plumbing.

ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 196 (public exclusions meet the residual consumer)

Re-ran the exact public residual audit with
`python n11-work/ops/lanes/C/certify_next512_row_cap.py`. It checked all 100
ordered DBM pairs for the seven public failures and reported all seven excluded
with strict margins from `7.39e-7` to `4.97e-5` (exact rationals retained in
`next512-row-cap-certificates.json`). This confirms that raising the dual row
cap cannot rescue any of the seven; the old 10/12/16-row experiment is moot for
the only residual records present publicly. Scope: host-side exact arithmetic
over public evidence, not kernel credit and not a statement about the 382
absent records.

Added `N11Formalization/EnergyTerminalBatchB13PublicResidualCanonical.lean`.
It instantiates last part's canonical packet exclusion with the existing
`FrozenCapPublicExcludedAggregate.PublicResidualData`, proves the exclusion for
every node, and derives
`canonical_producer_iff_radius_certificate`,
`radius_certificate_of_canonical_producer`, and
`canonical_producer_of_radius_certificate`. Thus the public tree supplies the
canonical-exclusion half of the producer interface, while the producer remains
exactly the residual radius obligation. Added the module to `TARGETS.txt` after
the residual certificate target. **CI pending**; no kernel claim.

Static scope only: `git diff --check` exited 0; forbidden-token scan found no
matches in the new module. `FrozenCapRowCapTreeBridges.lean:49` is now the
correct `end` line, unlike the earlier reported syntax failure. No local Lean
build was attempted. SHA256 (lowercase): new module
`d55aa9a67864887d1c75d2fd6713627bb88adafbbfd8d85118c423ecd1559c96`;
residual certificate module unchanged this part at
`6e19343d207165d8f6a0675a09eb508c28524d57412d5299d2ea39b73d5c3e40`;
`TARGETS.txt` `774e6c6a0cec518a572d5ef25289d493fbcf6caf3058cc078e53832bdd598099`.

Still unproved: the radius certificate for every residual id, including the
seven public ids; packet producer/canonicality; all 382 absent payloads;
seven-class and energy premises; root integration. The lane remains
mathematically blocked on the residual radius theorem. Very next concrete step:
read CI for the two lane-C targets; if the new bridge is red, fix its first
failing declaration, and if green, preserve it and seek geometric evidence for
the producer rather than any further row-cap search.

ROOT-IMPORT REQUEST: none.

## 2026-10-31 - part 197 (residual interface green; public tree repaired, CI pending)

Fetched CI run `41201323694` (source `3551ab87`) and read its build log.
`EnergyTerminalBatchB13ResidualCertificates` exited 0 with only the expected
axiom set `[propext, Classical.choice, Quot.sound]`; this is now **CI green**
for the residual certificate interface and its consumers. No residual id is
paid by that interface.

The same run found `FrozenCapPublicExcludedTree` **CI red** (`exit 1`) at all
seven branches: the row-cap goals used the core `y_*` vector while packet-cap
hoped for `yW_*`, and its strict-gain goals used `FlashCosine.Dq/DQ` and
`FlashCosineLeaf284Bridge.T` while the witness theorem used the corresponding
`FrozenCapRationalCore` constants. Repaired the file by rewriting each row-cap
branch with `yW_*` and adding definitional constants
`core_Dq_eq_flash`, `core_DQ_eq_flash`, `core_T_eq_flash` plus
`strict_gain_to_flash`; all seven strict-gain branches now use that transport.
This is a repair of a conditional exclusion tree, not a packet payment. The
dependent `FrozenCapPublicExcludedAggregate` and new
`EnergyTerminalBatchB13PublicResidualCanonical` remain **CI pending**.

Static scope: `git diff --check` passed; forbidden-token scan of the new
module passed. No local full Lean build attempted. SHA256 (lowercase):
`FrozenCapPublicExcludedTree.lean` updated; `TARGETS.txt` unchanged this part;
new bridge remains `d55aa9a67864887d1c75d2fd6713627bb88adafbbfd8d85118c423ecd1559c96`.
Exact SHA values for the tree are recorded by the supervisor after commit.

Still unproved: residual radius certificates for all 389 ids; packet/canonical
production from geometry; 382 non-public payloads; MPacket validity; energy and
seven-class premises; root integration. The public tree pays no id. Very next
concrete step: read CI for `FrozenCapPublicExcludedTree`, aggregate, and public
canonical bridge; if the tree remains red, fix its first new mismatch, and if
green, seek actual geometric producer evidence rather than more row-cap work.

ROOT-IMPORT REQUEST: none.
