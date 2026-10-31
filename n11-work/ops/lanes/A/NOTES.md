EXPERT (2026-10-31): Fresh run 41150468008 contradicts the session-76 "fixed" claim.
- `EndpointChecks.lean:257--259,277--279` still fail `omega`; after `fin_cases j`, replace each with `norm_num at hj` (or `exact absurd hj (by norm_num)`).
- First build only `SevenClassQ0Deg3EndpointChecks`; treat later reds as dependency-red until that exit is 0.
- Then serially require exit 0 for `UpperReductionUnimodal`, both suffixes, `EdgeShape`, all bins, `SectorAssembler`, and `TableBounds`.
- `TableBounds` does not identify `edges R` or construct `Degree3AreaCertificate`; after green target `areaCertificate_of_table ... (hedges : edges R = image ... ) : Nonempty (Degree3AreaCertificate h hr R)` with strict total.
- The 18,441-value decimal audit is not proof of `totalUpper < piLo`; no exclusion credit before that certificate.
- C450 completion is green but not root-imported; root integration is a supervisor action, not another C450 proof.

# Lane A notes

## Ledger

- C450 Main/audit are CI-green (run `41123531381`); this is the only paid Lane A
  result. `Cos/Mono/Bins` are green, but `EndpointChecks` exits 1 and every
  edge/sector module downstream is dependency-red at `cc04268c`.
- All sector-reduction modules from session 55 onward are **CI pending** or
  dependency-blocked; none is kernel-green.
- `SectorValid`, strict `totalUpper < piLo`, `Q0Degree3AreaInput`, all seven
  exclusions, and the arbitrary-centre theorem remain unpaid.

## 2026-10-30 (sessions 24--54, condensed)

Repaired the C450 chain, Cos/Mono/Bins, EndpointChecks, 21 edge peaks, both
negative-edge suffixes, and all 42 edge-shape facts. Earlier CI reds isolated
`Nat.mod_lt` arguments, opaque Taylor terms, an incompatible composite
derivative, `decide` table facts, and `norm_num`/`omega` ordering. Exact audits
(not proofs) passed: 8/8 endpoint bins, 2048 cosine steps, 21 edge shapes, and
the `9 x 2049` sector grid.

## 2026-10-30 (sessions 55--74, condensed)

Drafted the peak/calculus/shape/witness/bounds chain and all eight all-row bins
(with row-0 predecessors), using exact 72-bin argmax audits.  These modules and
their historical hashes are retained in git history; none is kernel-green and
all remain **CI pending**.
## 2026-10-31 (session 75) -- all-row sector assembler drafted

**Did.** Added `sectorBinUnimodal`, assembling the eight all-row bin theorems
(0--7) at the exact witness table `sectorBinWitness`, and `sectorValid`, which
combines it with the already emitted 72-bin peak theorem through
`sectorValid_of_bin_unimodal`.  This removes both explicit shape hypotheses
from the 72-bin reduction.  No strict-total, area-input, or exclusion claim is
made.

**Files / SHA256.**
`SevenClassQ0Deg3SectorAssembler.lean`
`b3e6c8cb35af9b8d9c6b0a2ae097e70832a068751606f2a0701e9fb30bc2c75c`.
`TARGETS.txt`
`69e7da488dc4c2408787188ba48bf42bafb72e421d0b68db2c7d768b5394e7b6`.

**Checks (scope).** `git diff --check`, forbidden-token scan, and `py_compile`
of the bin-6/7 audit PASS.  A Mathlib probe of the `fin_cases`/`first`
dispatch pattern exceeded its bounded 90 s startup timeout and produced no
verdict.  No project oleans exist locally and no Lean build was run, so this
module is **CI pending**, not kernel-green.

**Still unproved / unpaid.** Every sector Lean result remains CI pending.
Strict `totalUpper < piLo`, `Q0Degree3AreaInput`, the seven exclusions, and the
arbitrary-centre theorem remain unpaid.  In particular, `sectorValid` is not
yet a paid theorem until CI exits 0.

**Next concrete step.** Read CI's first failing line for `EndpointChecks` and
then this assembler.  If green, supply its `SectorValid` result to the strict
total assembly and locate the next concrete gap to `Q0Degree3AreaInput`; if
red, repair the named signature/import/tactic error before adding anything.

## 2026-10-31 (sessions 76--77, condensed)

CI run `41123531381` (`cc04268c`) failed first on stale `EndpointChecks`, not
the sector additions; current HEAD already has the repaired source.  Session
77 added `SevenClassQ0Deg3TableBounds`, combining `EdgeValid`, `SectorValid`,
and all 2049 node checks, plus `tableEdges` injectivity and
`edgeMax (tableEdges i) = edgeMaxAt i`.

`SevenClassQ0Deg3TableBounds.lean` SHA256
`d13a9d9caa98a5923a6b5ed5f64fe0981930b7d7f4eb7e456f27a7ff25cf5dbd`.
The exact rational grid audit passes (21 edge maxima, 18,441 sector values,
strict-total decimal slack `0.012092890371`), but no Lean build was run.
All sector/table Lean results remain **CI pending**.  Still unpaid: canonical
relabelling transport, strict total per actual cover, `Q0Degree3AreaInput`,
the seven exclusions, and the arbitrary-centre theorem.

## 2026-10-31 (session 78) -- table-to-certificate bridge drafted

**Did.** Added `SevenClassQ0Deg3TableCertificate`, proving
`certificate_of_canonicalTable`: `TableBounds` plus an equality of `edges R`
with the canonical 21-edge table, a `NineTies`, and the strict finite total
constructs `Degree3AreaCertificate`.  The proof wires the 2049-node table and
9-sector table directly, and rewrites the 21-edge family through
`edgeMax_tableEdges`; it does not duplicate any finite scan.  Also added the
direct contradiction form `false_of_canonicalTable`.

**Files / SHA256.**
`SevenClassQ0Deg3TableCertificate.lean`
`a24045fa1277909e672c1cc809750500157140739adaf20d3437dba5b56631d3`;
`TARGETS.txt` `6a8a8096562d922e05e303a33c7494b25f237f49888096b61628d8d186546664`.
The target adds `N11Formalization.SevenClassQ0Deg3TableCertificate`.

**Checks (scope).** `git diff --check` and forbidden-token scan PASS.  No Lean
build was run and no project oleans exist locally, so both new theorems are
**CI pending**, not kernel-green.  Their conclusions are conditional on the
explicit edge equality and strict-total hypotheses.

**Still unproved / unpaid.** The source degree-three theorem gives the table
only after `labelMap (canonicalPerm k b)`.  The inverse-label dual vector and
the nine sector indices must be transported through that permutation; the
strict total for every actual cover is still separate.  All seven exclusions
and the arbitrary-centre theorem remain unpaid.

**Next concrete step.** Define `renameMu p mu j := mu (p.symm j)` and prove
the finite edge-sum identity over `Finset.image p`, then use
`degree_three_table_graph` to replace its explicit canonical-edge hypothesis;
leave sector transport as the next named premise if it cannot be discharged
in the same module.

## 2026-10-31 (session 79) -- EndpointChecks branch repair (condensed)

CI run `41150468008` failed first at `SevenClassQ0Deg3EndpointChecks`, not the
later table targets.  Six `omega` branches could not use `hj : j.val < 5`
after `fin_cases` on `Fin 8`; both occurrence sites now use
`exact absurd hj (by decide)`.  Source SHA256
`926151016043881e69999e6f310b5e4933f06488a6e16518596b40c4bdb30ed7`.
The repair is **CI pending**.  A 180 s Mathlib probe timed out during
startup.  No theorem became paid; all relabelling, strict-total,
`Q0Degree3AreaInput`, exclusion, and arbitrary-centre obligations remain.

## 2026-10-31 (session 80) -- C450 handoff audit repaired; root import requested (condensed)

`verify_chain_completion.py` (`e84968159ae0c71757e175414ab5ce3973ce3657cc25a2b964bff6a772818bdb`)
now checks the actual CI order and reports root integration. `py_compile` and the
audit PASS (25 transfers, chunk order Source31/26/21/16/11, Source36 endpoint,
consumer signature, deterministic emitter match). CI run `41150468008` exited 0
for both `C450ChainCompletionMain` and `C450ChainCompletionAudit`; this does not
cover the root import. **ROOT-IMPORT REQUEST:** replace the two commented
`HARK-MISSING` imports near `N11Formalization.lean:1952` with active imports of
`N11Formalization.C450ChainCompletion` and `N11Formalization.C450ChainCompletionMain`.
Root integration and all downstream seven-class obligations remain unpaid.

## 2026-10-31 (session 81) -- relabelled table bridge drafted

**Did.** Added `SevenClassQ0Deg3RelabelledTableCertificate`.  Definitions
`renameMu`, `renameEdgeMax`, `renameSectorMax` pull the table back through an
arbitrary permutation.  `edge_bound_relabel` and `sector_bound_relabel` prove
the two finite bound families; `certificate_of_degreeThreeGraph` uses
`degree_three_table_graph` existentially, so it removes the explicit
canonical-edge premise from `certificate_of_canonicalTable`.  The only
remaining certificate hypothesis is the relocated strict finite total.

**Files / SHA256.** New Lean source
`8012f8be4f5be3e433d1fb6ad2925faae31a7e5fb81ccfb21d8afb0551f3fc46`;
`TARGETS.txt` `2caf12ce886f3de92d0d272a2fdb3b982d7630eb3e1606302a35c4f1988baca6`.
Target `N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate` added.

**Checks (scope).** `git diff --check` and forbidden-token scan PASS.  No Lean
build was run (no local project oleans), so all four new theorems are **CI
pending**, not kernel-green.

**Still unproved / unpaid.** The relocated strict total for every `k,b`, the
global sector/numeric chain to it, `Q0Degree3AreaInput`, all seven exclusions,
and the arbitrary-centre theorem remain unpaid.  CI has not yet checked the
new module or the earlier `TableCertificate`.

**Next concrete step.** Inspect CI's first error in the new module; if green,
prove the relocated strict-total equality to the canonical table total using
`sum_labelMap_pullback`, `cyclicSum_pullback`, and
`canonicalPerm_nextSite`, thereby reducing the hypothesis to the single
canonical strict inequality.

## 2026-10-31 (session 82) -- exact relabelled-total transport

**Did.** Added `totalUpper_relabel_eq` and `strict_relabel_iff` to
`SevenClassQ0Deg3RelabelledTableCertificate.lean`.  The proof reindexes the
21-edge sum along the injective `labelMap (canonicalPerm cut b)`, uses
`sum_labelMap_pullback` for every edge moment, reindexes the nine sector terms
with `cyclicSum_pullback`, and transports `nextSite` through
`canonicalPerm_nextSite`.  Thus the relocated strict total is exactly the
canonical `totalUpper ... mu ...`, not merely bounded by it.

**Files / SHA256.** `SevenClassQ0Deg3RelabelledTableCertificate.lean`
`215a917ee94cab78efdb3da345fb6184e29069ee6dfeea0da5722a73f1e61413`;
`TARGETS.txt` unchanged `2caf12ce886f3de92d0d272a2fdb3b982d7630eb3e1606302a35c4f1988baca6`.

**Checks (scope).** `git diff --check` and forbidden-token scan PASS.  No local
project oleans or Lean build; both lemmas are **CI pending**, not kernel-green.

**Still unproved / unpaid.** No theorem is yet instantiated with the canonical
strict inequality; the global numeric/sector chain, `Q0Degree3AreaInput`, all
seven exclusions, and the arbitrary-centre theorem remain unpaid.

**Next concrete step.** Refactor `certificate_of_degreeThreeGraph` to extract
`cut,b,hedges` and invoke `strict_relabel_iff` once, yielding a consumer whose
only strict premise is the single canonical `totalUpper ... < piLo`; inspect CI
before adding downstream dispatch.

## 2026-10-31 (sessions 83--84, condensed)

Added the canonical strict-total constructor and
`q0Degree3AreaInput_of_strictTotal`: one universal canonical total premise
over length-one `OrderedData` runs constructs `Q0Degree3AreaInput`, deriving
`hq`, `hd`, and `NineTies`.  Final source hash
`3372659dffe845844da5d10c984668f3510f8679ee3de44872636c5a0b650485`.  These
are **CI pending**.  The canonical strict finite total and all downstream
exclusions remain unpaid; next is to inspect the first CI error.

## 2026-10-31 (sessions 86--87, condensed)

Replaced the six impossible branches at
`SevenClassQ0Deg3EndpointChecks.lean:257--259,277--279` with `norm_num at hj`.
File hash `edc83db80cd8e7c2d680716632dd167cf12264c00edb4100fdadad1eb12fe5c9`;
exact endpoint audit PASS (8/8 rational bins), `git diff --check` and token scan
PASS.  Run `41150468008` predates this uncommitted repair, so its exit 1 gives
no verdict.  The probe's `Mathlib.lean` is prelude-only and cannot test the
pattern.  All later sector/edge targets remain CI pending/unpaid.

## 2026-10-31 (session 88) -- CI provenance audit; next-target source audit

**Did.** Confirmed the repaired `EndpointChecks` hash above is newer than the
recorded CI commit (`24e434b4`; run `41150468008` still reports exit 1).
Audited `SevenClassQ0Deg3UpperReductionUnimodal.lean`: its 21 separated peak
checks and `edgeValid_of_unimodal` case split are structurally consistent;
CI, not source inspection, must decide it.  No Lean change was needed.

**Checks (scope).** `project_status.py --check` PASS (handoff manifest only);
`git diff --check` and forbidden-token scan PASS at current worktree.  No
project Lean build; all sector theorems remain **CI pending**, not green.

**Still unproved / unpaid.** `EdgeMonotone`, strict canonical total,
`Q0Degree3AreaInput`, all seven exclusions, and arbitrary-centre theorem.
C450 Main/audit are CI-green but not root-imported.

**Next concrete step.** After supervisor commits, require CI exit 0 for
`EndpointChecks`; otherwise repair its first reported error.  Only then inspect
the first `UpperReductionUnimodal` error, serially.

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).
