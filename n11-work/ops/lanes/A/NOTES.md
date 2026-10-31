EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 111): the completed CI log identified unreduced vector
witness lookups as the first peak owner. Both peak proof sets now rewrite each
witness through a bounded kernel-decided equality before exact rational
evaluation. The repairs are **CI pending**; C450 completion remains CI-green.

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

Run `41182882564` exposed unexpanded `edgeUpper`/`edgeCoeff` and unresolved
`nextSite`. Repairs added direct imports/opens and explicit `norm_num`
unfoldings; exact edge/grid audits passed. A further hidden dependency in
`EdgeShape` was fixed and `check_q0_degree3_imports.py` now passes all 47
explicit references over 38 modules. These are source/arithmetic checks, not
kernel credit; both peaks and downstream targets remained **CI pending**.

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

## 2026-10-31 (sessions 105--106, condensed)

Refuted the proposed global adjacent-step sector premise; replaced it with
per-bin certified maxima and fixed-bin witnesses. Exact 72-bin audits and Lean
witness binding passed. These are arithmetic/source checks, not kernel credit.

## 2026-10-31 (session 107) -- CI first-owner diagnosis and peak repairs

Pulled the public Lean job `41193732877` (commit `ae211d7a`). Its target log
shows the first owning errors: `UpperReductionUnimodal:17` declared a `[local
simp]` attribute for `edgeCoeff` before that constant existed, and
`SectorPeak` left all nine peak goals unsolved because `norm_num` could not
normalize the emitted 3,840-bit exact fractions. Moved the edge simp attribute
after the `edgeCoeff` definition. Changed the sector emitter to emit certified
six-decimal upward rational enclosures of the audited maxima; an exact
`Fraction` assertion checks `max ≤ bound < max + 10^-6` for every row.

**Files / SHA256.** `SevenClassQ0Deg3UpperReductionUnimodal.lean`
`67cdeda1ebdba1c0f041fef28e8447b209f615931d6a2d2cb4f0987285ddb3ec`;
`SevenClassQ0Deg3SectorPeak.lean`
`94f5ac911461516fe9b98aa41adc7e47f551ac7980731130bd3040bded5dae68`;
`emit_q0_degree3_sector_peak.py`
`8832884f3ab6cb2a4d4efc7260fc8f0fcd8f55ed4c49970f53f3a98510167f06`.

**Checks (scope).** Bound audit PASS 9/9; `py_compile`, forbidden-token scan,
and `git diff --check` PASS. These are source and exact-arithmetic checks. No
Lean build ran locally. Both modules remain **CI pending**; `41193732877` is
evidence of the old failures, not credit for these repairs.

**Still unproved / unpaid.** Kernel acceptance of the peak repairs and
`EdgeShape`; analytic edge/sector shape obligations; bins/assembler/table;
strict-total; `Q0Degree3AreaInput`; seven exclusions; arbitrary-centre theorem.

**Next concrete step.** After supervisor commit, inspect the new run's
`UpperReductionUnimodal` and `SectorPeak` exits. If both are green, use the
first owning error in `EdgeSuffixNonpos`/`EdgeShape`, not a dependency-red
descendant.

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
