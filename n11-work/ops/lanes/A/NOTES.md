# Lane A notes

CURRENT (session 162): lane A still has no kernel verdict; the sole blocker is
CI ordering/routing.  Supervisor action is required.

## Ledger

- CI-green paid Lane A targets: `C450ChainCompletionMain`,
  `C450ChainCompletionAudit`, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and
  `UpperTables`.
- Repair only the first owning error; dependency-red descendants are not
  diagnostics.  After green prove `q0_degree3 : Q0RunExclusion 1`; this is 1/7.
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

## 2026-11-01 (sessions 155--156) -- bin-3 audit and old peak failures

Exact row-0 bin-3 audit passed 256 nodes / 32,640 pairs (minimum drop
`3.216484420446041e-05`); exact source scope only.  Run `41182882564` showed
the old monolithic peak failures were table unfolding plus an unqualified
`nextSite`; the split fixes both.  Peak-split/projection/import source checks
PASS.  Probe timed out and lacked Mathlib oleans, hence no kernel verdict.

**Files / SHA256.** `check_q0_degree3_peak_max_projection.py`
`ca94478e58d2062c2c38473b5f2e54d4b0e5636e0e9bd90cafac84011ff58aed`;
`check_q0_degree3_edge_peak_split.py`
`199f2a135dc53fe957cf6aa58caf477e18ef825d92726dcb239de3f7814ca25f`;
`check_q0_degree3_sector_peak_split.py`
`8116335b536744368ab67825e5cc005d7df0c9691eea0d0eeed8409ac84ff4f0`.

**Still unproved / unpaid.** All split peaks and downstream shape/calculus,
bins, strict total, `Q0Degree3AreaInput`, `Q0Exclusion`, the other six
exclusions, and the arbitrary-centre theorem remain CI pending/unpaid.

**Next concrete step.** Get an A-first isolated CI job.  If it is green through
`UpperReductionUnimodal` and `SectorPeak`, proceed to the first shape/suffix
owner; if not, use the projected-literal probe pattern to diagnose that exact
row without changing the audited arithmetic.

## 2026-11-01 (session 157) -- peak provenance bound; exact CI stop located

Hardened `emit_q0_degree3_sector_peak.py`: it now parses `sectorMax` from
`SevenClassQ0Deg3UpperTables.lean`, recomputes all nine sector values at the
Lean `piHi`, asserts equality with that table, and reports stale JSON metadata
instead of trusting it.  Exact recomputation gives witnesses
`[1024,1536,1536,1536,1536,1536,1536,1536,1024]`.

The JSON metadata is indeed stale: `witnessK` differs at rows 1 and 8, and all
eight `sectors[i].max` literals were produced at a different `piHi`/row offset
than the Lean table.  I did not edit the frozen JSON; the Lean base now has an
explicit exact binding to the maintained table.

**Files / SHA256.** `emit_q0_degree3_sector_peak.py`
`9e71ee65fe914b4ce4cc7403fcdca01fe57b8da63660e80f8802208c8a4ffcbb`.
The other only working-tree change is this note.  `TARGETS.txt` is unchanged.

**Checks (scope).** Emitter exit 0; all nine maxima equal `sectorMax` exactly;
all 12 generated sector-peak Lean files were byte-identical before/after;
`py_compile` and `git diff --check` PASS.  This is exact rational/source
evidence, not Lean elaboration or kernel credit.

**CI evidence.** Public run `41318867156` at `5dc953ab` reached
`[9344/9351]`, then was killed with exit 143 while elaborating
`EnergyTerminalBatchB13RefineSixteenResidualCensusMain` (about 7.3 GB RSS,
only seconds before termination).  No lane-A target starts in that job.
`C450ChainCompletionMain` did replay with exit 0 as a dependency of an
exit-0 lane-B target, so that integration remains CI green at this head.

**Still unproved / unpaid.** All split peaks, sector bin shape/witness/bins,
strict total, `Q0Degree3AreaInput`, all exclusions, and the arbitrary-centre
theorem remain without a current lane-A kernel verdict.

**Next concrete step.** Supervisor-only workflow fix: build lane A before C/B,
or run lane A in a separate job.  Lane A cannot edit the workflow under its
ownership rules.  Once dispatched, inspect `UpperReductionUnimodalPeak00` and
`SectorPeak00` first, then the assemblers.

## 2026-11-02 (session 158) -- first owning CI errors fixed; Q0 source blocker
Retrieved the public failure log for run `41352871085` at `b1e15e83`.  The
aggregate job says success, but individual target exits are red: lane A's
`UpperReductionUnimodalPeak00` and `SectorPeak00` both exited 1, as did
`StrictTotal` and `Q0Exclusion`.  The first owning error for the sector chain
was `SevenClassQ0Deg3SectorPeakBase.lean:69:8: Unknown identifier
sectorValid_of_unimodal` (an unqualified `#check` after the namespace closed).
The first owning edge error was `SevenClassQ0Deg3UpperReductionUnimodalBase.lean:78`
`hcoeff`: all 21 cases left the literal rational equal to an unreduced
two-element `Finset.sum`.
Fixed both owners: qualified the sector `#check`, and made the 21 coefficient
equalities explicitly reduce `Finset.sum_insert`/`Finset.sum_singleton` before
`norm_num`.  No arithmetic value, peak, or frozen module was changed.  These
are **drafted / CI pending**, not kernel credit.  Local kernel probes were not
usable: the probe Mathlib oleans are absent and even `example : (1:Nat)=1 := by
rfl` timed out in this contended sandbox.

`StrictTotal`/`Q0Exclusion` are blocked upstream by frozen
`SevenClassQ0Deg3.lean`: line 77 uses unknown `ringOnlyTriangles` (its import
closure lacks `ActualHubTriangleCensus`), and its axiom report contains
`sorryAx`.  Fixing that requires a supervisor decision because the file is
frozen and must not be edited in place.

**Files / SHA256.** `SevenClassQ0Deg3SectorPeakBase.lean`
`77c4f6fa8f3ea3d81357239cb578241c2796a275360f58395107f58fc38fe5ec`;
`SevenClassQ0Deg3UpperReductionUnimodalBase.lean`
`f2cfc5e863df59e2b4b6251be4210d58d8c882cab1955e745608b3b52ff1f5c4`.
`TARGETS.txt` unchanged (both files are imported by existing targets).

**Checks (scope).** Log extraction and exact error attribution only; emitter
and notes checks PASS.  No Lean elaboration verdict exists locally.

**Still unproved / unpaid.** Peak/module assembling, edge shape, all 72 sector
bins, strict total, `Q0Degree3AreaInput`, all seven exclusions, and the
arbitrary-centre theorem remain unproved.  `C450ChainCompletionMain` replayed
with exit 0 in this run.

**Next concrete step.** CI rerun of lane A; inspect `Peak00` and `SectorPeak00`
for the next owning error (the earlier reports only exposed the base failures).

## 2026-11-02 (sessions 159--161) -- repaired q0 base; no CI reach

`SevenClassQ0Deg3Repaired.lean` (SHA256
`40ada549c3ac5e6f8a002be2c423336e366901eafec9c3c0f82e412e72f0b04c`) is
generated by `emit_q0_degree3_repaired.py` from frozen SHA
`48d41f5d…75b61`, adding only `ActualHubTriangleCensus` and
`open ActualRefinementEarCount`; `TableCertificate` imports it.  Emitter,
byte-transform, frozen-SHA, 960-module closure, targeted banned-token, and
`git diff --check` checks PASS (source only, no kernel verdict).  Run
`41352871085` never reached lane A: lane B OOMed (exit 137).  Thus
`Repaired` through `Q0Exclusion` remain CI pending and unpaid.

## 2026-11-02 (session 162) -- live CI routing audit

Queried GitHub Actions for branch `n11/work`.  Latest commit `efaa0d39` has a
successful `Scoped mathematical replay` run `41373241981`, but no
`n11-lean-build` run: the push did not touch a Lean/TARGETS path.  Therefore
`SevenClassQ0Deg3Repaired` through `Q0Exclusion` still have no kernel verdict;
the green math workflow is unrelated.

The Lean workflow is a single serial target loop ordered **C, B, A**.  The
lane-local audit reports `lane order: C B A`, `lane A position: 3`, and fails
reachability because lane A depends on C/B finishing.  Lane B previously
stalled/OOMed, so adding lane-A files alone cannot obtain a verdict.

**Files / SHA256.** No Lean source changed this session.  Audit script
`audit_ci_lane_a_reachability.py`
`78fb25e63f7209c33f00eabb1a110f61c9ffbe099770c548289c1e17a65d053d`;
`TARGETS.txt`
`714a4d8a758749695a29c3655e3df8e077af63e229dd8730271e09ce2bddc6bb`;
workflow
`0eea35515dd4cba4478fdbb8056abc5909815f2fbb504cc9a14e1ee9ca62b4f1`.

**Checks (scope).** GitHub run metadata/live branch query and source-level
workflow-order audit PASS.  `project_status.py --check` PASS (handoff only).
No Lean build or kernel check ran.

**Still unproved / unpaid.** `Repaired`, `TableCertificate`,
`RelabelledTableCertificate`, `StrictTotal`, `Q0Exclusion`, peak/shape/bin
assembly, `Q0Degree3AreaInput`, all seven exclusions, and the arbitrary-centre
theorem remain unpaid.

**Next concrete step.** Supervisor must put `ops/lanes/A/TARGETS.txt` before C/B
in `n11-lean-build.yml` (or create an isolated A job), then trigger a Lean-path
change.  Worker then reads the first own error at `SevenClassQ0Deg3Repaired`.
