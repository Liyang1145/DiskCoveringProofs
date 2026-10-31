EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
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

## 2026-10-31 (session 106) -- sector-bin audit bound to Lean witnesses

Added an independent exact-`Fraction` replay that binds the 72 witness values
in `SevenClassQ0Deg3SectorBinWitness.lean` to the first exact bin argmax and
checks every adjacent step. All 72 maxima are unique and match the Lean table.
All 18,369 within-bin steps split exactly as 8,724 up then 9,645 down. All 63
inter-bin jumps replay and are upward. The witnesses are at the first point
for 31 bins, the last point for 32 bins, and interior for 9 bins. The existing
bins modules already expose one Lean shape theorem per bin and the assembler
combines them; this audit validates the exact numerical targets behind those
drafts, but does not replace kernel checking.

**Files / SHA256.** `audit_q0_degree3_sector_bin_lean.py`
`84c982299a22e5ba6177d5bd36521bd4b5c532003a97309443c2c04dc1b95ccd`;
`q0-degree3-sector-bin-lean-audit.json`
`480265a36803927891e43313981bfc5f22da3eb59fc00c5ed5474706bdef9532`.

**Checks (scope).** `timeout 90s python3 audit_q0_degree3_sector_bin_lean.py`
PASS: source/report hashes, 72/72 witness bindings, 18,369/18,369 within-bin
adjacent steps, and 63/63 inter-bin jumps. `py_compile`, forbidden-token scan,
and `git diff --check` PASS. Regression sweeps also PASS: import closure 47/47
over 38 modules, the 72-bin single-peak audit, and the canonical strict-total
audit (slack `0.012092890370999`). No Lean build ran; this is exact arithmetic
and source-binding evidence, not kernel proof credit.

**Still unproved / unpaid.** Kernel acceptance of the drafted 72-bin shapes,
`SectorAssembler.sectorBinUnimodal`, and `SectorAssembler.sectorValid`, plus
the pending peak/edge chain; table/strict-total, `Q0Degree3AreaInput`, seven
exclusions, and arbitrary-centre theorem remain unpaid. No theorem is paid by
this arithmetic audit.

**Next concrete step.** After the supervisor commits, require CI exit 0 for
the bins modules, `SectorAssembler`, `TableBounds`, and `TableCertificate`;
diagnose the first owning-module error rather than a dependency-red aggregate.
Do not duplicate the already-drafted endpoint-witness reductions.

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

At `2026-10-31T12:26:10Z`, public run `41195990232` (commit `cc16dff4`, job
`124526826288`) was still `in_progress`, started `11:37:23Z`; GitHub exposes no
target exits until completion. Re-ran both explicit-unfold gates: edge PASS
21/21 and sector PASS 9/9. The repaired source hashes remain edge
`67cdeda1…`, sector `94f5ac91…`, emitter `8832884f…`. `project_status.py
--check` also passed, but that is a handoff-index/manifest check only, not math
or full-file integrity.

**Still unproved / unpaid.** The run's `UpperReductionUnimodal`, `SectorPeak`,
`EdgeSuffixNonpos`, `EdgeShape`, bins/assembler, table/strict-total,
`Q0Degree3AreaInput`, seven exclusions, and arbitrary-centre theorem have no
new kernel credit. The local audits establish source binding, not proofs.

**Next concrete step.** Poll run `41195990232`; if complete, read target exits
and the first owning error in the earliest red module. If still running, do not
start a speculative repair; wait for owner diagnostics.
