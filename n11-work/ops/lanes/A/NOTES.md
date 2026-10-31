EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 103): peak repairs and exact audits pass; executable gates
enforce sector namespace resolution and explicit unfolding in all 21 edge and
9 sector peaks.
The Lean repairs are uncommitted and remain **CI pending**. C450 completion is
CI-green; root integration remains a supervisor action.

## Ledger

- CI-green paid Lane A targets: `C450ChainCompletionMain`,
  `C450ChainCompletionAudit`, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and
  `UpperTables`.
- At commit `7f7e6f3b`, the first lane reds were `UpperReductionUnimodal` and
  `SectorPeak`; every later edge/sector/table target was dependency-red.
- `SectorValid`, strict `totalUpper < piLo`, `Q0Degree3AreaInput`, all seven
  exclusions, and the arbitrary-centre theorem remain unpaid.

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).

## 2026-10-31 (session 102) -- executable gate for explicit peak unfolding

The supervisor has not yet committed the session-101 repair: `HEAD` is
`66629de7` and `SevenClassQ0Deg3UpperReductionUnimodal.lean` plus this file are
still modified. The active run `41190760154` therefore tests the older file;
at 10:24 UTC its live log was still building `C450Source27GroupedC18`, so no
fresh lane-A exit exists.

Added `check_q0_degree3_edge_peak_unfold.py`, a textual pre-CI gate that parses
all `edgePeakValid_*` proofs and requires exactly indices 0--20 and an explicit
`norm_num` list containing `EdgePeakValid`, `edgeUpper`, `edgeCoeff`,
`tableEdges`, and `nodeQ`. This directly prevents the observed failure where
the local simp attribute did not override an explicit `norm_num` list.

**Files / SHA256.** `check_q0_degree3_edge_peak_unfold.py`
`ae8e2cbf43ee3393bedeb83a15a5466596e1e7454d2241dafe89e8509b679029`;
`SevenClassQ0Deg3UpperReductionUnimodal.lean`
`55ddf09e9a5bad01cca0a42c4facc4d1c1c8921bc8fb0f2d14d57c7693377576`;
`SevenClassQ0Deg3SectorPeak.lean`
`4a7b94f8619c82cca4b632d111f8114f9158c40d15d87e53bdf71454ede34ad0`.

**Checks (scope).** The gate PASSes 21/21 explicit unfoldings; `py_compile`,
forbidden-token scan over both peak modules, and `git diff --check` PASS. These
are source/shape checks only. No local Lean build ran. Both peak modules remain
**CI pending** and are not proof credit.

**Still unproved / unpaid.** Kernel acceptance of both peak modules, all edge
and sector monotonicity shape obligations, downstream bins/table/strict-total
targets, `Q0Degree3AreaInput`, the seven exclusions, and the arbitrary-centre
theorem.

**Next concrete step.** After supervisor commit and the next CI run, require
exit 0 for `UpperReductionUnimodal` and `SectorPeak`; then diagnose the first
owning-module failure in `EdgeSuffixNonpos`, not the dependency-red aggregate.

## 2026-10-31 (session 101) -- explicit `edgeUpper` unfolding repair

Downloaded the complete job log for run `41182882564` (job `124490443415`).
All 21 `edgePeakValid_*` failures still displayed a literal outer `edgeUpper`.
The explicit `norm_num [...]` list overrides `[local simp]`, so the session-99
attribute did not unfold `edgeUpper`; it had to be named in each `norm_num`
list. Added it to all 21 checks in
`n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperReductionUnimodal.lean`.
The sector failure in that log was the already-repaired unresolved `nextSite`;
its file and emitter now reproduce byte-for-byte and need a fresh CI run.

**Files / SHA256.** `SevenClassQ0Deg3UpperReductionUnimodal.lean`
`55ddf09e9a5bad01cca0a42c4facc4d1c1c8921bc8fb0f2d14d57c7693377576`;
`SevenClassQ0Deg3SectorPeak.lean`
`4a7b94f8619c82cca4b632d111f8114f9158c40d15d87e53bdf71454ede34ad0`;
`emit_q0_degree3_sector_peak.py`
`bcfd6bc7531af9df98f8387cf74aae7c6e26303efe62c26cdfff09fe41493fd5`.

**Checks (scope).** `audit_q0_degree3_edge_unimodal.py` PASS: exact rational
replay of 21/21 increasing prefixes, decreasing suffixes, witnesses, and peak
maxima (`q0-degree3-edge-unimodal.json` SHA256
`2a0a38b150cae0b9d200c90f273084b3bdbd4f51d43f4eca1270d8ea5b2f412f`). Sector
grid replay also PASS: 21 edge maxima, all `9 x 2049` sector values, and the
strict total (slack `0.012092890370999008`; audit JSON SHA256
`bc0dd05c4dd7a38f08ae98d916a1eff5bbe8b7db98bdd53749278049215669b9`). Sector
emitter reproduction PASS (identical SHA256). `git diff --check` and
forbidden-token scan PASS (only `#print axioms` matched `axiom`). No local Lean
build; the owning target remains **CI pending**. `project_status.py --check`
also PASSed, but that checks handoff manifest declarations only, not math or
full file integrity.

**Still unproved / unpaid.** Kernel acceptance of both repaired modules; the
edge/sector monotonicity shape obligations; downstream bin/table targets;
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-centre theorem.

**Next concrete step.** After the supervisor commits, read the new run's target
exits. If both peak modules are green, trace the next red in dependency order
from `EdgeSuffixNonpos`/`EdgeShape`/`SectorShape`; otherwise use the first new
owning-module error, not the aggregate exit.

## 2026-10-31 (session 100) -- exact first-blocker diagnosis from run log

Fetched the completed public job log for run `41182882564` (commit `7f7e6f3b`)
from the GitHub API. The summary file in `ops/ci/LATEST.md` is stale (it still
lists this run as pending/in-progress), and the run's overall `success` marker
does not override the red target exits.

The exact lane-A failures were:
- `UpperReductionUnimodal`, lines 58, 63, 68, ..., 158: all 21 peak proofs
  ended with unsolved goals whose display still contained literal `edgeUpper`
  (and, for some edges, an unreduced `edgeCoeff` sum). This confirms the missing
  unfolding of `edgeUpper`/`nodeQ`, not bad peak arithmetic.
- `SectorPeak`, lines 35, 42--43, 49--50, and every peak theorem: repeated
  `Unknown identifier nextSite`, with consequent unsolved goals. This confirms
  that importing/opening `ActualRingLinkBoundaryData` transitively through
  `UpperTables` was insufficient.

The worktree already contains the corresponding fixes from session 99:
`attribute [local simp] edgeUpper nodeQ edgeCoeff tableEdges` in
`SevenClassQ0Deg3UpperReductionUnimodal.lean` (extended this session to force the
observed residual coefficient sums to reduce), and a direct import plus absolute
`open N11Formalization.ActualRingLinkBoundaryData` in
`SevenClassQ0Deg3SectorPeak.lean` and its emitter. Current SHA256:
`SectorPeak` `4a7b94f8619c82cca4b632d111f8114f9158c40d15d87e53bdf71454ede34ad0`;
`UpperReductionUnimodal` `6e7eee916a2d684aa71b7c3a009248ff790e462aa004ddce0edfa42e181eb1a3`;
Both fixes remain **CI pending** because they are uncommitted here.

**Checks (scope).** Read-only extraction from the 417 MB run log; no local Lean
build. A bounded Mathlib-probe attempt to reproduce the `simp`/`norm_num`
unfolding timed out at 120 s while importing Mathlib, so it supplies no result
and is not evidence. No target was paid.

**Still unproved / unpaid.** Kernel acceptance of both repairs; all downstream
edge/sector/bin/table targets; `SectorValid`; canonical strict total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-centre theorem.

**Next concrete step.** After supervisor commits and CI completes, read target
exits plus the first owning-module error. If these two modules are green, inspect
`EdgeSuffixNonpos` next (it was dependency-red on `UpperReductionUnimodal`), then
`EdgeSuffixHigh`, `EdgeShape`, `SectorShape`, and later table targets.

## 2026-10-30 (sessions 24--74, condensed)

Repaired the C450 chain, Cos/Mono/Bins, EndpointChecks, 21 edge peaks, both
negative-edge suffixes, and all 42 edge-shape facts. Drafted the peak/calculus/
shape/witness/bounds chain and all eight all-row sector bins from exact 72-bin
argmax audits. Exact audits (not proofs) passed: 8/8 endpoint bins, 2048 cosine
steps, 21 edge shapes, and the `9 x 2049` sector grid. Historical hashes are in
git history; downstream modules remain CI pending.

## 2026-10-31 (sessions 75--84, condensed)

Added `SectorAssembler`/`sectorValid` and `TableBounds`, combining `EdgeValid`,
`SectorValid`, node checks, edge-table injectivity, and canonical edge maxima.
Added `TableCertificate` and the relabelled bridge, proving that the actual
cover supplies the canonical permuted table; the bridge reduced the strict
premise to one canonical finite total. Exact 72-bin and grid audits passed.
All Lean results remain **CI pending**; no theorem was paid by arithmetic.

## 2026-10-31 (sessions 86--92, condensed)

Repaired the six impossible `Fin 8` endpoint branches with the prior
`exact absurd hj (by decide)` strategy. Run `41168580187` then exposed
`UpperTables:83` using `nextSite` outside its namespace; added the direct import
and open to Lean and emitter. Final `UpperTables` SHA256
`e18374eca3ac8923739850d66a826cf1cc84c58758bfce963f7aa467e24788a9`;
emitter `99f2ca079a19c4b1997aa7243d5dab6cf2f019b978500f2dfaa751d63bdffca7`.
Exact audits confirmed 21 singly peaked edges, 9 x 2049 sectors, and total slack
`0.012092890371`. These are arithmetic checks only.

## 2026-10-31 (sessions 93--97, condensed)

Added `verify_q0_degree3_strict_total.py` (total `3.129499763218794...`, Lean-
`piLo` slack `0.012092890370999...`). Added `SevenClassQ0Deg3StrictTotal.lean`
and its emitter, rounding the canonical 21-edge/9-sector ledger upward and
proving `canonicalTableTotal_lt_piLo`. Session 97 replaced the false relabelled
total equality with a fixed-grid equality to `canonicalTableTotal`, so
`q0Degree3AreaInput_of_strictTotal` now has the single canonical strict premise
and derives `q0Degree3AreaInput`. All remains **CI pending**, not proof credit.

## 2026-10-31 (session 98) -- observed first lane-A failures

Run `41182882564` (commit `7f7e6f3b`) had overall conclusion `success` but
target-exit data contradicting it: `UpperReductionUnimodal` and `SectorPeak`
exited 1 (`nextSite` unresolved; all 21 edge checks left `edgeUpper` unexpanded).
Those session-98 edits were not in that commit; the marker is not proof credit.

## 2026-10-31 (session 99) -- hardened repairs and exact-data replay

Hardened `SectorPeak` with a direct `ActualRingLinkBoundaryData` import and the
absolute `open N11Formalization.ActualRingLinkBoundaryData`, eliminating the
observed name-resolution failure. Updated its emitter to reproduce the import
and open. Hardened the edge repair to `attribute [local simp] edgeUpper nodeQ`,
so the existing 21 `norm_num` peak checks unfold both definitions.

**Files / SHA256.** `SevenClassQ0Deg3SectorPeak.lean`
`4a7b94f8619c82cca4b632d111f8114f9158c40d15d87e53bdf71454ede34ad0`;
`emit_q0_degree3_sector_peak.py`
`bcfd6bc7531af9df98f8387cf74aae7c6e26303efe62c26cdfff09fe41493fd5`;
`SevenClassQ0Deg3UpperReductionUnimodal.lean`
`ba0c95df6c2fa0214430449f51434f07d4919ab967b8566792c8c5e1833d3229`.
`TARGETS.txt` is unchanged at
`ce6fe00c282cadd87789f33b07b249708650e4da7082b79ab92d0e94922160ff`.

**Checks (scope).** Sector emitter reproduction, `py_compile`, forbidden-token
scan, and `git diff --check` PASS. Exact `Fraction` replays PASS: 21/21 edge
single peaks and maxima; 9/9 sector maxima over all 2049 nodes; exact total with
slack `0.012092890370999008` (`q0-degree3-sector-grid-audit.json` SHA256
`bc0dd05c4dd7a38f08ae98d916a1eff5bbe8b7db98bdd53749278049215669b9`). No local
Lean build ran. Both repairs are **CI pending**, not kernel-green.

**Still unproved / unpaid.** Kernel acceptance of the repairs and of the
relabelled/strict-total modules; the analytic edge/sector shape obligations;
sector/table assembly; `Q0Degree3AreaInput`; all seven exclusions; and the
arbitrary-centre theorem.

**Next concrete step.** After supervisor commit, inspect target exits from the
new run. If `UpperReductionUnimodal`, `EdgeSuffix*`, `EdgeShape`, and
`SectorPeak` are green, continue in dependency order through
`SectorShape`/`SectorCalculus`/the bin modules to `TableBounds`,
`RelabelledTableCertificate`, and `StrictTotal`; otherwise fix the first new
error from its owning module.

## 2026-10-31 (session 103) -- sector-peak regression gate

CI remained stale at run `41182882564`/commit `7f7e6f3b`; no fresh exits exist
for the pending repairs. Static review of `EdgeSuffixNonpos` found no safe edit
without kernel feedback. Added a textual pre-CI gate for the two observed
`SectorPeak` failure modes: it requires the direct
`ActualRingLinkBoundaryData` import and absolute open, and all nine
`sectorPeakValid_*` proof `norm_num` lists to name every needed unfolding
(including `sectorUpper`, `nodeBin`, `nextSite`, `nodeQ`, and the sine brackets).

**Files / SHA256.** `check_q0_degree3_sector_peak_unfold.py`
`58fc498dcac3c1fc621268860b31e412243fc8ed024063133e9c1333c7dff22f`;
`check_q0_degree3_edge_peak_unfold.py`
`ae8e2cbf43ee3393bedeb83a15a5466596e1e7454d2241dafe89e8509b679029`;
`SevenClassQ0Deg3UpperReductionUnimodal.lean`
`55ddf09e9a5bad01cca0a42c4facc4d1c1c8921bc8fb0f2d14d57c7693377576`;
`SevenClassQ0Deg3SectorPeak.lean`
`4a7b94f8619c82cca4b632d111f8114f9158c40d15d87e53bdf71454ede34ad0`.

**Checks (scope).** Both gates PASS (21/21 edge and 9/9 sector checks), plus
`py_compile` on the new gate. These are source-shape checks only; no Lean build
ran. Both peak modules remain **CI pending** and are not proof credit.

**Still unproved / unpaid.** Kernel acceptance of both peak modules; all edge and
sector shape obligations; downstream bins/table targets; `Q0Degree3AreaInput`;
the seven exclusions; and the arbitrary-centre theorem.

**Next concrete step.** After the supervisor commits, require exit 0 for
`UpperReductionUnimodal` and `SectorPeak` in the new CI run, then diagnose the
first owning-module error in `EdgeSuffixNonpos` rather than a dependency-red
aggregate.
