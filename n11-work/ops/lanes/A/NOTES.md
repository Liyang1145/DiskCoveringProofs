# Lane A notes

CURRENT (session 104): peak repairs and exact audits pass, and the next hidden
dependency break in `EdgeShape` is fixed. A new import-closure gate passes all
47 explicit q0-degree-three references over 38 modules. The peak and downstream
Lean targets remain **CI pending**. C450 completion is CI-green; root
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

## Sessions 100--101 (condensed) -- peak repairs from the run log

Run `41182882564` showed literal `edgeUpper`/`edgeCoeff` residues in all 21
edge peaks and unresolved `nextSite` in every sector peak. Session 99 fixed the
import/open, and session 101 added `edgeUpper` explicitly to every `norm_num`
unfolding list (the explicit list overrides `[local simp]`). Exact edge and
sector-grid replays passed; both modules remained **CI pending**.

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

## 2026-10-31 (session 104) -- repair hidden EdgeShape dependency

The checkout contains the session-101/103 peak repairs (`HEAD ae211d7a`); the
fresh n11 Lean job `41193732877` is queued. Static import tracing found that
`SevenClassQ0Deg3EdgeShape.lean` used
`SevenClassQ0Deg3EdgeSuffixHigh.edgeDecFrom_twelve` and
`..._thirteen` without importing `EdgeSuffixHigh`; the old dependency-red run
could not expose this. Added the direct import. Added
`check_q0_degree3_imports.py`, which computes transitive import closures and
fails on any explicit q0-degree-three module reference outside them.

**Files / SHA256.** `SevenClassQ0Deg3EdgeShape.lean`
`69a24f050ad38d692f25758d081a882c73377cf254b5e840ac8b3ba9a837b28c`;
`check_q0_degree3_imports.py`
`0d313a8ef8fa95bd5832c23b73eedc0864e79bb07e0c93529a43bebf98702b8c`.

**Checks (scope).** Import gate PASS: 47 references across 38 modules; both
existing peak-unfolding gates PASS 21/21 and 9/9; `py_compile`,
forbidden-token scan, and `git diff --check` PASS. These are source/dependency
checks only. No local Lean build ran, so this is not kernel proof credit.

**Still unproved / unpaid.** Kernel acceptance of both peak modules and the
repaired `EdgeShape`; all edge/sector shape obligations; downstream bins/table/
strict-total targets; `Q0Degree3AreaInput`; seven exclusions; arbitrary-centre
theorem.

**Next concrete step.** After the supervisor commits and CI completes, require
exit 0 for `UpperReductionUnimodal`, `SectorPeak`, `EdgeSuffixNonpos`,
`EdgeSuffixHigh`, and `EdgeShape`; then use the first new owning-module error
from `SectorShape`/`SectorCalculus` or the bin chain as the next bounded target.

## 2026-10-31 (session 105) -- global sector adjacent-step premise refuted

Extended the exact sector-grid audit to test the proposed `SectorIncSteps` /
`SectorDecSteps` adjacency reduction. Every one of the nine rows refutes both
global premises despite reproducing its listed maximum: sector 0--1 first rise
at `k=543`, sectors 2/8 at `1173`, 3/7 at `1051`, 4/6 at `1076`, and 5 at
`1070`. Each row also has post-witness rises at bin boundaries (one for most,
three for sectors 0--1). Therefore `SectorAdjacentUnimodal` cannot be paid as
stated; the session-61 per-bin correction is mandatory.

**Files / SHA256.** `audit_q0_degree3_sector_steps.py`
`9eb71438f968deb925d890419109dcf28695e99e7fd8fecd8ee2181b16ce686f`;
`q0-degree3-sector-steps-audit.json`
`4e1354be1b1c9529be9d016373c412aef30d39b7f6787de90424708305bf1067`.
The pre-existing grid audit remains byte-identical at
`bc0dd05c4dd7a38f08ae98d916a1eff5bbe8b7db98bdd53749278049215669b9`.

**Checks (scope).** Both exact-`Fraction` audits PASS: 21 edge maxima, all
`9 x 2049` sector values, strict total (slack `0.012092890370999008`), all nine
maxima, and explicit adjacent-step counterexamples in every row. Import gate
PASS 47/47. `py_compile`, forbidden-token scan, and `git diff --check` PASS. A
bounded Mathlib probe timed out importing Mathlib, so it is not evidence. No
Lean target was built; all Lean results here remain **CI pending**. Arithmetic
refutation is not kernel proof.

**Still unproved / unpaid.** Kernel acceptance of the repaired peaks/edge shape;
a valid per-bin sector shape; `SectorValid`; downstream bins/table/strict-total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-centre theorem.

**Next concrete step.** Rephrase `SectorAdjacentUnimodal` per bin (monotone on
the increasing portion(s) of each fixed-bin interval and antitone on decreasing
portions), then exact-audit every within-bin adjacent step and every inter-bin
jump before changing Lean.
