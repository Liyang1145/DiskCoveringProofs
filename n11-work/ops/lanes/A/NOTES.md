# Lane A notes

CURRENT (session 168): the q0 first-owner repairs are **drafted / source
preflight PASS / CI pending**.  The latest completed lane-A log was from run
`41378003343` (job `125062414500`, HEAD `016484e6`); it confirms the old
failures, not the repaired files.  Run `41380560959` at `a29e4ee1` was still in
progress and its log was not yet downloadable.  No kernel credit is claimed.

## Ledger

- CI-green paid Lane A targets: `C450ChainCompletionMain`,
  `C450ChainCompletionAudit`, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and
  `UpperTables`.
- Repair only the first owning error; dependency-red descendants are not
  diagnostics.  A green q0 chain would prove `q0_degree3 : Q0RunExclusion 1`
  (1/7).
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions
  or raised heartbeats.
- `SectorValid`, strict `totalUpper < piLo`, `Q0Degree3AreaInput`, all seven
  exclusions, and the arbitrary-centre theorem remain unpaid.

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).

## Condensed history

- Sessions 115--153 exactly audited 21 edge peaks, 21 discrete peaks, 18,441
  sector points, 72/72 bins, 18,369 within-bin steps, 63/63 jumps, and bin-3
  (256 nodes / 32,640 pairs).  Global sector unimodality was refuted; the valid
  route is bin-wise.  These are source/arithmetic checks, not kernel credit.
- Sessions 142--153 split 21 edge and 9 sector peaks and repaired the bin-3
  half bound.  All split/calculus/bin/table modules remain CI pending.
- C450/Main/Audit, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and `UpperTables`
  are CI-green.  Root still carries both HARK markers.
- Sessions 158--162 found and repaired earlier base errors, then identified CI
  lane routing as the reachability blocker.  Session 159 introduced
  `SevenClassQ0Deg3Repaired.lean`, a generated copy of frozen SHA
  `48d41f5d3a71c41adc3ff0af26f86740b2f4ed82383a037d182aac0f16075b61`
  adding only the missing census import and ear-count open.
- Sessions 165--166 made the strict-total division bounds goal-shaped with
  `div_le_div_of_nonneg_right`; exact ledger checks passed, but no Lean verdict
  was obtained.
- Session 167 read the live log of run `41378003343`.  First owners were the
  repaired-copy import placement, nine sector peak rational comparisons, and
  the 21 edge coefficient equalities.  The log's peak goal reduces to a huge
  fraction-to-fraction inequality; the edge goal reduces to a literal rational
  versus a two-term `Finset.sum`.  Fixes: move provenance below imports and add
  terminal `decide +kernel` to those bounded closed rational goals.  No frozen
  module, arithmetic table, or theorem statement changed.

## 2026-11-02 (session 168) -- old log confirmed; repaired tree audited

Re-downloaded run `41378003343` and inspected the exact goals: sector peak 01
reduces to an exact fraction inequality, while the edge `hcoeff` case «1»
reduces to `643066…1523 / 200…0000 = ∑ x ∈ {1,2}, …`.  This confirms that the
declared terminal kernel suffix targets the actual residual shapes rather than
an unrelated simplification step.  Regenerated all repaired modules
deterministically and reran the sector split-preservation checker.  Added
`audit_q0_degree3_kernel_repairs.py`, which checks import placement, both kernel
suffixes, banned tokens in all 11 repaired modules, and `TARGETS.txt`
registration.

The exact-rational emitter independently recomputed all nine sector maxima and
they equal `SevenClassQ0Deg3UpperTables.sectorMax`.  The older
`q0-degree3-piecewise-8.json` metadata is stale at sector rows 0--8 and witness
rows 1/8; the emitter already binds to recomputed exact values and prints the
drift, so this is not substituted by a cached maximum.

**Files / SHA256.**
`SevenClassQ0Deg3Repaired.lean` `37317833f1bc1d1066edc0f3cb866069657d27f39826bf4f6c93bd014517d3d3`;
`SevenClassQ0Deg3UpperReductionUnimodalBase.lean`
`3e38d206b45fe1bb6bf7c2f020d862ea37294862085b93cf71849e5c5585519b`;
`emit_q0_degree3_repaired.py`
`94674838008d6d3a1a0d65dc48b5614a444e815565e9f8694b0bd54211c2233f`;
`emit_q0_degree3_sector_peak.py`
`84ae09862ea1001a9cdc1216a1d1bfb2ac9abc4d43705ab07fd2110922bc6736`;
`split_q0_degree3_edge_peak.py`
`4cc9cb0bf28ef780df2e125269667b40d0de3d3afa05522bd47810278e9b6765`;
`audit_q0_degree3_kernel_repairs.py`
`10b7ff7f3e03d708295098f91619efa26d99981cb0366bb2bdaf447d2cf5ca45`.
Sector rows 00--08 SHA256:
`0762019a6f0b612e0ecf67f1c27f1e210a2bd352153ea759ef5e9fa5102a5755`,
`e4445823acf3dfcb0f79098c6c70356e021d715b9d3181f08b3399f541562f23`,
`a8bad4c1df79ba728a0bc6203dac3334d3db9082e8871aed41b78f8ade5dcc51`,
`880dff4aff0e88fa27950028456eb042900a12fb19440c6f78ba5d9a1b2f0af3`,
`42a849e914cec8c0c5eefdb2487fbc7530256ba55f0a95c6e895187e4ef202b3`,
`4214989487644b4d491cfa4a898ceac785dd64c8ba225e01932edd9f6fd18d9d`,
`c4d5a4ac6a91e311d52b559947dd51482d64cc849e0fcf825f03cbce7a33742e`,
`228cf7cf4cc1a59c1fb7d812c8eb9b6c786046ed1426fb08f7fb8d148b91752a`,
`1a57e4243c23f7b4ebee11dfd406200ab9a3c1f12ce82df581bf42c1b32eff13`.

**Checks (scope).** Deterministic emitter reruns PASS; sector split preservation
9/9 PASS; new source preflight PASS; `py_compile`, targeted banned-token scan,
and `git diff --check` PASS.  Exact Python recomputation matches all nine table
maxima.  A tiny local Lean probe (`Rat` inequality plus reflexivity) timed out
at 30 s, so there is **no local kernel verdict**; `decide +kernel` syntax and
elaboration remain CI-pending.

**Still unproved / unpaid.** `StrictTotal`, `Q0Exclusion`, all peak/shape/bin
assemblers, `Q0Degree3AreaInput`, the other six exclusions, and the
arbitrary-centre theorem remain CI pending/unpaid.  The in-progress run is not
evidence for this repaired worktree.

**Next concrete step.** Supervisor commits this worktree, then CI must reach
lane A and build `SevenClassQ0Deg3Repaired`, the nine `SectorPeak` rows, and
`UpperReductionUnimodalBase`.  Inspect the first owning error after
`SevenClassQ0Deg3Repaired`; if a kernel suffix fails, replace only that closed
goal with an explicitly rewritten rational comparison.


## 2026-11-02 (sessions 169--174, condensed) -- CI boundary and repair audits

No n=11 Lean job has existed for the repaired tree: runs `41380560959` and
`41399703011` are pending with no jobs; older runs predate the repairs.  Six
sessions therefore produced source/arithmetic evidence only, never a kernel
verdict.  Useful results: the q0 import-closure checker was corrected (skip a
file's own namespaces) and `SevenClassQ0Deg3Q0Exclusion` was found not to import
`SevenClassQ0Deg3`; adding that direct import moved the closure audit to PASS
(115 references across 76 q0 modules).  `audit_q0_degree3_kernel_cost.py`
records literal sizes sent to terminal `decide +kernel`: sector peaks 00--08
have 2071--2099-bit largest literals, the edge module 141-bit.  A core-only
363-bit Rat probe timed out at 50 s and is inconclusive, not a rejection.
Strict-ledger exact arithmetic PASS with total `3.135646999268476` and slack
`0.005945654321317` (Python rationals, not Lean).  Other rerun preflights
(sector split 9/9, edge split 21/21, q0 repair, unfold/max projection) PASS in
their source-check scopes.  All q0 Lean modules remain CI pending; the other
six exclusions, `Q0Degree3AreaInput`, strict total, and the arbitrary-centre
theorem remain unpaid.

## 2026-11-02 (session 175) -- q0(5,8) graph matched; source coefficients not exact

Extended the seven-class graph audit from the q0(4,9) pilot to the q0(5,8)
closure case.  New script `audit_q0_degree5_graph.py` verifies that
`q0_closure_dual_0_3.json` declares `start=0, span=3`, 11 faces and 21 edges and
that its labelled face set and edge set equal `ActualOrderedMetricGraphs.q0Faces 3`
(reconstructed independently from `q0Fan`/`centralFace`).  It also checks the
certificate header (`strict=true`, same span), 121 coefficients, 121 `z` slots,
and the 11+9+9 factor-label order.  Result: **PASS_SOURCE_GRAPH_AND_LAYOUT_ONLY**,
`q0-degree5-graph-match.json`, sha256
`8daf9efdd67f7349de92533ceb750f633cebd16f006b1dcb88566dae99285c00`;
script sha256 `9dca117fd1904fbdaf1656f343a8757dde0fb59cdfa991119a544bd44db32bdb`.

Material finding: unlike the q0(4,9) pilot, the q0(5,8) certificate stores all
121 coefficients as **decimal strings** and `z` as binary floats, not exact
rational pairs.  This file therefore cannot be a Lean coefficient source; an
exact-rational certificate must be regenerated by the source emitter before a
`Q0Degree5FiniteTable` can be written.  No factor bound, balance, or exclusion
is proved by this audit.

**Checks run (scope).** The new graph/layout audit above; `python
tools/project_status.py --check` PASS (handoff index only).  No Lean build; CI
still shows run `41399703011` pending with no job, so every q0 module and the
new audit's (nonexistent) kernel claims remain CI pending/unpaid.

**Files.** Added `audit_q0_degree5_graph.py` and `q0-degree5-graph-match.json`.
No Lean, TARGETS, frozen, root, or toolchain file changed.

**Still unproved / unpaid.** q0(4,9)/q0(5,8)/q1(3,9)/q1(4,8)/q1(5,7)/q1(6,6)
tables, all exact factor bounds, the seven exclusions, energy, and the
arbitrary-centre theorem.  q0(5,8) additionally lacks exact rational
coefficients.

**Next concrete step.** Regenerate q0(5,8) coefficients from the committed
source emitter in exact `Fraction` form and extend the audit to compare the
emitter's graph/field order; only then emit `Q0Degree5FiniteTable.lean`.

## 2026-11-02 (session 176) -- q0(5,8) exact-decimal source reconstructed

Added `reconstruct_q0_degree5_exact.py`, which parses
`q0_closure_dual_0_3.json` with `parse_float=Fraction` (so the stored decimal
literals, not their binary-float images, are authoritative), verifies the
SciPy emitter's 121-slot layout (`mu` 9, `hub` 2, `side` 21, `radius` 18,
`angle_slack` 21, `lambda` 1, `eta` 1, `linear` 39, `closure` 9), checks all
21 angle slacks are nonnegative and `eta = 0`, and checks that the 121
9-place certificate coefficients equal the rounded source vector in order.
It writes `q0-degree5-exact-source.json` with numerator/denominator pairs and
the Lean-reconstructed 11-face/21-edge graph.

**Files/shas.** emitter above `456217278a0cde9c4cdd2beaa0893031fdc0f2e4cfea6b27599d292240d3a12e`;
exact source `900d2186b5321acc8dc522f44f483c483355a3a7cbef4ea7c7d9817ad717f41d`;
prior graph audit `9dca117fd1904fbdaf1656f343a8757dde0fb59cdfa991119a544bd44db32bdb`;
graph report `8daf9efdd67f7349de92533ceb750f633cebd16f006b1dcb88566dae99285c00`.

**Checks (scope).** Exact reconstruction PASS (121 rational coefficients:
45 negative, 49 positive, 27 zero; max denominator `10^18`; 21/21 angle
slacks nonnegative; certificate copy/order check 121/121); graph/layout audit
PASS; `py_compile` PASS; banned-token scan of the new Python PASS;
`git diff --check` PASS. No Lean file was emitted and no kernel claim is made.

**Still unproved / unpaid.** The q0(5,8) factor upper bounds, exact strict
total, `Q0FiniteTable 3`, the other six finite tables, and the arbitrary-centre
theorem remain unpaid. Exact decimal coefficients alone prove no factor bound.

**Next concrete step.** Emit `Q0Degree5FiniteTable.lean` data definitions from
the rational pairs plus the reconstructed graph, using the existing
`FiniteCanonicalCertificate` interface; then add its target and request CI to
kernel-check the first owning elaboration error before attempting factor
certificate terms.

## 2026-11-02 (session 177) -- q0(5,8) Lean source data emitted

Added deterministic `emit_q0_degree5_source_data.py`, which reads the
hash-bound `q0-degree5-exact-source.json` and emits
`Q0Degree5SourceData.lean`.  The module contains all 121 exact rational
coefficients grouped as `mu`(9), `hub`(2), `side`(21), `radius`(18),
`angle_slack`(21), `lambda`(1), `eta`(1), `linear`(39), `closure`(9), plus
the canonical sorted 11-face and 21-edge arrays.  It states graph identities
to `q0Faces 3` / `q0Edges 3` by bounded `decide +kernel`; TARGETS now includes
`N11Formalization.Q0Degree5SourceData`.

**Files/shas.** Lean module `f2f18661b1ad85b10e95d1f00443ac48cc07d9c436b5a6ad2817e8e8b0a660c8`;
emitter `ad089df5be8571eba8f832d27c6d63798dba9102072815ad3266b8775bae0819`;
input exact source `900d2186b5321acc8dc522f44f483c483355a3a7cbef4ea7c7d9817ad717f41d`.

**Checks (scope).** Emitter run PASS; `py_compile` PASS; TARGETS registration
PASS; source counts/groups inherited from the PASS exact reconstruction.  A
stripped-import syntax probe in `mathlib-probe` timed out at 90 s with no
output, so it is **inconclusive**, not a Lean verdict.  No project build was
run; module is CI pending and no kernel claim is made.

**Still unproved / unpaid.** The semantic slot map from source groups to
`CanonicalCoeffQ` (`faceMask`, side/left/right first/second, switchMask,
width), `kap`, balance, all face/switch/sector bounds, strict total,
`Q0FiniteTable 3`, and the remaining six finite tables.

**Next concrete step.** Inspect the q0 degree-four pilot or source emitter to
map `side`/`radius`/`linear` slots to `CanonicalCoeffQ`, then generate the `D`
definition and let CI report the first owning elaboration error.

## 2026-11-02 (session 178) -- q0(5,8) canonical slot map checked

Added `map_q0_degree5_canonical_data.py`, which reads the hash-bound exact
source and records the direct `CanonicalCoeffQ` map: `mu=z[0:11]`,
`sideFirst=z[11:32]`, `sideSecond=z[73:94]`, radius/linear copy pairs at
`z[32+2i]`/`z[33+2i]` and `z[94+2i]`/`z[95+2i]`, `width=z[71]`, `eta=z[72]`,
`switchMask=-1`, and face masks by first/second opposite-edge ownership. It
checks 11 triangular faces, all 21 opposite edges, and the group cardinalities.

**Files/shas.** script `166b5aa414d592726c75f5f5b9217702224052070c33efd116ffc7a89dfc70e4`;
map `q0-degree5-canonical-map.json` `55a2ecce715c88195b12e66186010ff8ded691cfba85b3dff2eee8733ffae126`.

**Checks (scope).** Mapping audit PASS; `py_compile` PASS. No Lean build.
The 21 `angle_slack` slots are likely `kap`, but the nine `closure` LP slots
have no direct `CanonicalCoeffQ` field, so do not emit `D` as complete yet.

**Next concrete step.** In `q0_closure_dual.py`, eliminate/absorb the nine
closure multipliers and verify the remaining coefficient signs against
`canonicalFaceB`/`canonicalSwitchB`; then emit the Lean `D`/`kap` definitions.
