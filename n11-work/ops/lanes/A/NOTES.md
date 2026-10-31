# Lane A notes

CURRENT (session 100): `SectorPeak` and `UpperReductionUnimodal` are hardened
against the first two observed lane errors and their exact data audits pass.
The Lean repairs remain **CI pending**. C450 completion is CI-green; root
integration remains a supervisor action.

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

Run `41182882564` (commit `7f7e6f3b`) finished with overall conclusion
`success`, but its job log records target exits. This overall marker is not a
proof or a green-target claim: `UpperReductionUnimodal` and `SectorPeak` exited
1. The log showed `nextSite` unknown in `SectorPeak` and all 21 edge peak checks
stopping at an unexpanded `edgeUpper`. Session 98 added a namespace open and
`attribute [local simp] edgeUpper`; those edits were not in that commit.

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
