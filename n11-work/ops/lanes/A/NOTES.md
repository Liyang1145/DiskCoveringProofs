EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 113): both peak repairs pass their static gates but have not
yet been kernel-checked. The latest repository CI (`41201323694`, commit
`3551ab87`) predates the dirty-worktree repairs; C450 completion is CI-green.

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

## Sessions 98--104 (condensed) -- peak chain repair and import gate

Repaired missing unfolds/imports and the hidden `EdgeShape` dependency; the
47-reference import gate passed. These were source checks, not kernel credit.

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

Repaired six impossible `Fin 8` endpoint branches and `UpperTables` imports;
exact audits confirmed 21 peaks, the `9 x 2049` sector grid, and slack
`0.012092890371`. These are arithmetic checks only; hashes are in git history.

## 2026-10-31 (sessions 93--97, condensed)

Added `verify_q0_degree3_strict_total.py` (total `3.129499763218794...`, Lean-
`piLo` slack `0.012092890370999...`). Added `SevenClassQ0Deg3StrictTotal.lean`
and its emitter, rounding the canonical 21-edge/9-sector ledger upward and
proving `canonicalTableTotal_lt_piLo`. Session 97 replaced the false relabelled
total equality with a fixed-grid equality to `canonicalTableTotal`, so
`q0Degree3AreaInput_of_strictTotal` now has the single canonical strict premise
and derives `q0Degree3AreaInput`. All remains **CI pending**, not proof credit.

## 2026-10-31 (sessions 105--106, condensed)

Refuted the proposed global adjacent-step sector premise; replaced it with
per-bin certified maxima and fixed-bin witnesses. Exact 72-bin audits and Lean
witness binding passed. These are arithmetic/source checks, not kernel credit.

## 2026-10-31 (session 107, condensed) -- first-owner peak repairs

Run `41193732877` exposed the pre-move `edgeCoeff` attribute and unsolved
sector peaks from oversized exact fractions. The attribute was moved after the
definition; the sector emitter switched to certified six-decimal upward bounds.
Files/hashes are in git history. Bound audit PASS 9/9; `py_compile` and
`git diff --check` PASS. These are source/arithmetic checks, and the repairs
remained **CI pending**.

## 2026-10-31 (session 108) -- post-commit CI owner check queued

Confirmed run `41193732877` completed with conclusion `success` despite target
exits `1`; it tested the pre-repair commit `ae211d7a`, not the current tree.
Its first lane-A reds remain the already-repaired `UpperReductionUnimodal:17`
unknown `edgeCoeff` and unsolved peak goals. The current repair hashes are
unchanged from session 107.

Checked the public API: commit `cc16dff4` has Lean run `41195990232` (job
`124526826288`) **in progress**, so neither the peak repairs nor any downstream
target has kernel credit yet. This is stronger evidence than the stale
`LATEST.md` entry, but still not CI-green.

**Still unproved / unpaid.** Kernel acceptance of both peak modules and
`EdgeShape`; analytic edge/sector shape; bins/assembler/table/strict-total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-centre theorem.

**Next concrete step.** Poll public run `41195990232` to completion and inspect
jobs/logs. Record actual exits for `UpperReductionUnimodal` and `SectorPeak`;
if green, diagnose the first owning error in `EdgeSuffixNonpos`/`EdgeShape`.

## 2026-10-31 (session 109) -- pending run rechecked; source audits pass

At 12:26Z run `41195990232` (job `124526826288`) was still in progress. Both
explicit-unfold gates then passed edge 21/21 and sector 9/9; hashes remained
edge `67cdeda1…`, sector `94f5ac91…`, emitter `8832884f…`. `project_status.py
--check` passed, but only checks the handoff index, not math or full integrity.

**Still unproved / unpaid.** The run's `UpperReductionUnimodal`, `SectorPeak`,
`EdgeSuffixNonpos`, `EdgeShape`, bins/assembler, table/strict-total,
`Q0Degree3AreaInput`, seven exclusions, and arbitrary-centre theorem have no
new kernel credit. The local audits establish source binding, not proofs.

**Next concrete step.** Poll run `41195990232`; if complete, read target exits
and the first owning error in the earliest red module. If still running, do not
start a speculative repair; wait for owner diagnostics.

## 2026-10-31 (session 110) -- completed-run diagnosis and peak index fix

Run `41195990232` (commit `cc16dff4`) completed at 12:35Z. Its artifact shows
`UpperReductionUnimodal` and `SectorPeak` exit 1, making later q0 targets
dependency-red; C450 completion remains exit 0. The first owner reported
`UpperReductionUnimodal:17:39 Unknown constant edgeCoeff` (the pre-move
attribute at that commit), plus peak goals. The run log shows `SectorPeak`
leaves all nine goals with finite-vector coercions such as
`↑↑(![1024,...] 2)` unreduced after `norm_num`.

Updated both peak proof sets to normalize `Fin.val_ofNat` and `Fin.val_mk`
during the same rational evaluation. Synced the sector emitter. New SHA256:
`UpperReductionUnimodal` `501b2178763e82333a7ad5402bb2787363c20016b8afca0e153027762b5ec41b`;
`SectorPeak` `954bbec394b52a354251b2e7f4ec200fb0eda750bc02e6c2c8158cc899ff81c2`;
sector emitter `07d70382e9db3ea5922d0ef97bd66e29c141c8ea069902ac443352084a63939e`.

**Checks (scope).** Artifact exits above; emitter `py_compile` PASS; explicit
unfold gates PASS edge 21/21 and sector 9/9. These are source/static checks;
no Lean build ran locally. Both peak repairs are **CI pending**.

**Still unproved / unpaid.** Kernel acceptance of both peaks; edge/sector
shape; bins/assembler/table/strict-total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-centre theorem.

**Next concrete step.** On the next committed run inspect the actual exits for
`UpperReductionUnimodal` and `SectorPeak`. If an unsolved peak remains, verify
whether `Fin.val_ofNat` fired before changing any finite table; otherwise take
the first owner error from `EdgeSuffixNonpos`/`EdgeShape`.

## 2026-10-31 (session 111) -- completed-run log diagnosis and witness rewrite

Fetched job `124526826288` for run `41195990232` (commit `cc16dff4`). The job
completed `success`, but the target list still records exits `1` for
`UpperReductionUnimodal` and `SectorPeak`; all later q0 targets are
dependency-red. C450 completion remains exit `0`. The run's first peak goals
show concrete rational comparisons with `↑↑(![...] 5)` left unreduced, despite
`Fin.val_ofNat` and `Fin.val_mk`; the stale `Unknown constant edgeCoeff` is also
present at line 17 of that pre-repair module.

Each of the 21 edge and 9 sector peak proofs now first performs
`rw [show <witness> i = (v : Fin 2049) by decide +kernel]`, then evaluates the
named rational expression with `norm_num`. The sector emitter emits the same
shape from the audited `witnessK` values. This is at most one literal Fin
equality per peak, not a large kernel decision.

**Files / SHA256.**
`SevenClassQ0Deg3UpperReductionUnimodal.lean`
`b91a55c3e65345299824a4c5938045ff49d6d113ecffed0fa421bf25aa1faf3e`;
`SevenClassQ0Deg3SectorPeak.lean`
`36b77e3e4f283b6ef9c31bff30a398e9f0a8ad8ba8995ffca6238ef07623276b`;
`emit_q0_degree3_sector_peak.py`
`5b1691f199f367a9cfcde4781bc019ee08a1cf1b8a8a6757fede8ca562f778a1`;
edge gate `801d37898dad12c3e0cf785ff1fbf6c356b91336974a2b686c851e2226d81718`;
sector gate `5c32c482b4793a8c04cf674048fd3cae640d28315498e61afe6c02625a96ccf0`.

**Checks (scope).** CI log diagnosis above; both textual gates PASS edge 21/21
and sector 9/9 while requiring `decide +kernel` witness rewrites; emitter
`py_compile`, Python checks, and `git diff --check` PASS. No Lean build ran
locally (project oleans absent); both repairs remain **CI pending**. The
Mathlib probe attempt was killed by bounded timeout under host I/O load and
proves nothing.

**Still unproved / unpaid.** Kernel acceptance of both peaks; edge/sector
shape; bins/assembler/table/strict-total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-centre theorem.

**Next concrete step.** After supervisor commit, inspect the new run's actual
exits for `UpperReductionUnimodal` and `SectorPeak`. If green, take the first
owner error from `EdgeSuffixNonpos`/`EdgeShape`; if a witness `decide +kernel`
fails, replace it with a separately checked `(witness i).val = v` lemma.
## 2026-10-31 (session 112) -- owner-level peak fixes

Fetched run `41201323694` logs. `UpperReductionUnimodal` failed all 21 peaks
because `norm_num` re-unfolded `edgeWitness` after the explicit witness `rw`,
leaving `↑↑(![...] i)`; removed `edgeWitness` from those simp sets. The sector
module also targeted `sectorPeakAt` (nine rounded six-decimal upper bounds) rather
than `SectorValid`'s `sectorMax`; exact comparison shows `sectorPeakAt > sectorMax`
in all nine rows, with maximum excess `9.928e-7`, so the old peak theorem could not
discharge `SectorValid`. `SectorPeakValid` now compares directly to `sectorMax`.

**Files / SHA256.** `SevenClassQ0Deg3UpperReductionUnimodal.lean`
`ab0c7e865c0745a83540a1c80fdbb3eababc5867d341249bc6974818d2a7faee`;
`SevenClassQ0Deg3SectorPeak.lean`
`f2f3f3824bee0ff95999557d4483fd6762eee5ca485add83305de751078ff068`;
sector emitter `3b89619ab57fe5647358e9c3e05d42f86a85e22e85b54a24e073cd6ea9cfc6fb`.
sector gate `8afd1198b04e09d00eee8f69b2fcc6c059a688189225d23c544750682f68ea80`.

**Checks (scope).** CI log diagnosis above; edge/sector textual unfold gates PASS
21/21 and 9/9; emitter `py_compile` and `git diff --check` PASS. Independent exact
replay PASS: 21 edge maxima, all 18,441 sector points, strict slack
`0.012092890370999008`, and `sectorPeakAt > sectorMax` in 9/9 rows. The sector gate
now enforces `SectorPeakValid ≤ sectorMax`
(SHA256 `8afd1198b04e09d00eee8f69b2fcc6c059a688189225d23c544750682f68ea80`).
No project Lean build ran locally; Mathlib probe timed out under load. Both
repairs are CI pending.

**Still unproved / unpaid.** Kernel acceptance of both peaks; edge/sector shape;
bins/assembler/table/strict-total; `Q0Degree3AreaInput`; seven exclusions; and the
arbitrary-centre theorem.

**Next concrete step.** After supervisor commit, inspect the next CI exits. If a
peak remains red, reproduce its first goal in a tiny module and test the witness
normalization independently; otherwise take the first owner error in
`EdgeSuffixNonpos`/`SectorShape`.

## 2026-10-31 (session 114) -- CI artifact still pre-repair

Rechecked the maintained CI artifact: it still identifies run `41201323694` /
commit `3551ab87`, and its peak exits are `1` for
`UpperReductionUnimodal`, `SectorPeak`, `EdgeSuffixNonpos`, and `SectorShape`.
This is the already-diagnosed pre-session-112 tree, not a verdict on the dirty
repairs. `git status` confirms both repaired peak modules and their lane scripts
remain uncommitted; no new CI run is available to inspect.

**Checks (scope).** Read-only inspection of `ops/ci/LATEST.md` and worktree
status. The attempted Python extraction of the embedded summary was rejected
because the stored block is truncated; `rg` confirmed the four exit values.
No Lean or arithmetic check ran in this short continuation.

**Still unproved / unpaid.** Both repaired peaks still await kernel acceptance;
all downstream edge/sector/table/strict-total, `Q0Degree3AreaInput`, the seven
exclusions, and the arbitrary-centre theorem remain unpaid.

**Next concrete step.** After the supervisor commit triggers a new run, inspect
the first owner exit among the two peaks, then `EdgeSuffixNonpos`. If
`UpperReductionUnimodal` is still red, test its first witness-normalization goal
in a tiny module under `/workspace/tools/mathlib-probe`; do not build the full
project locally.
