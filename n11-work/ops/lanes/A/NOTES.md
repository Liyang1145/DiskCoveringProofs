CURRENT (2026-10-31, session 94): the `EndpointChecks` regression is repaired;
require its CI exit 0 first, then serial exits for `UpperReductionUnimodal`,
both suffixes, `EdgeShape`, all bins, `SectorAssembler`, and `TableBounds`.
`TableBounds` still needs canonical `edges R` and strict `totalUpper < piLo`
before `Degree3AreaCertificate`; decimal audits are not proof. C450 completion
is CI-green but root integration remains a supervisor action.

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
## 2026-10-31 (session 75, condensed)

Added the all-row sector assembler and `sectorValid` from the eight bin
theorems and 72-bin peak reduction. Exact audits and static checks passed, but
no Lean build ran: **CI pending** and no exclusion credit.

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

## 2026-10-31 (session 78, condensed) -- table-to-certificate bridge

Added `SevenClassQ0Deg3TableCertificate`, proving
`certificate_of_canonicalTable`: `TableBounds`, canonical edge equality,
`NineTies`, and strict finite total construct `Degree3AreaCertificate`.
SHA256 `a24045fa1277909e672c1cc809750500157140739adaf20d3437dba5b56631d3`.
Conditional and **CI pending**; relabelling and per-cover strict total remain.

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

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).

## 2026-10-31 (sessions 89--92, condensed) -- `UpperTables` dependency repair

Run `41168580187` found `UpperTables:83` using `nextSite` without its namespace;
`EndpointChecks` was green and later exits were dependency-red. Added
`import N11Formalization.ActualRingLinkBoundaryData` and
`open ActualRingLinkBoundaryData` to both Lean and emitter. Final SHAs:
`SevenClassQ0Deg3UpperTables.lean`
`e18374eca3ac8923739850d66a826cf1cc84c58758bfce963f7aa467e24788a9`;
`emit_q0_degree3_upper_tables.py`
`99f2ca079a19c4b1997aa7243d5dab6cf2f019b978500f2dfaa751d63bdffca7`.
Emitter reproduction, `py_compile`, forbidden-token scan, and exact rational
audits passed (21 singly peaked edges; 9 x 2049 sectors; slack
`0.012092890371`). Arithmetic checks only; no theorem was paid.

## 2026-10-31 (session 93) -- exact canonical strict-total audit

**Did.** Added `verify_q0_degree3_strict_total.py`, which parses the emitted
Lean `mu`, `lam`, `tableEdges`, `edgeMaxAt`, and `sectorMax` and independently
replays the exact `totalUpper` formula.  It also accounts separately for the
Lean 20-digit `RatInterval.piLo/piHi` and the 40-digit values in the older
manifest.  Exact result under the Lean constants: `3.129499763218794...`,
slack `0.012092890370999...`; the manifest total agrees to `9.02e-22` after
the intentional pi-precision substitution.  This confirms the strict-total
premise is numerically credible, but it remains an arithmetic audit, not a
Lean proof. **Files / SHA256.** `verify_q0_degree3_strict_total.py`
`4aff53fe1dc7ac55ba05c6df5e060c535ce3a382680ffd2876a631342198b45a`.
No Lean source or target changed.
**Checks (scope).** Exact `Fraction` replay and `py_compile` PASS; the audit
asserts equality to the JSON total, equality of its slack, and strictness
against the Lean `piLo`.  CI run `41172673380` is green but predates lane-A
commits and is not evidence for these sources. **Still unproved / unpaid.**
`canonical_strictTotal` has not been formalized;
`Q0Degree3AreaInput`, all seven exclusions, and the arbitrary-centre theorem
remain unpaid.
**Next concrete step.** Add a deterministic emitter for a new module proving
`totalUpper R mu lam piHi 2048 edgeMax sectorMax = C` under the canonical table
edge equality, then prove `C < piLo` by `norm_num`; CI must build it before any
strict-total credit is claimed.

## 2026-10-31 (session 94) -- reverted `EndpointChecks` strategy regression

**Did.** Session 93's fresh CI diagnosis plus commit history showed `51cdab56`
regressed six impossible-`Fin 8` branches from the known-good
`exact absurd hj (by decide)` to `norm_num at hj`. Restored all six branches in
`endpointUBin_le_one_of_lt5` and `nodeQ_binHi_le_two_of_lt5`.

**File / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`926151016043881e69999e6f310b5e4933f06488a6e16518596b40c4bdb30ed7`.
This is byte-identical to the file at CI-green run `41168580187` commit
`0f022bfb`; `TARGETS.txt` is unchanged.

**Checks (scope).** `git diff --check` and forbidden-token scan PASS; SHA cross
check against commit `0f022bfb` PASS. The same source built `EndpointChecks`
green in run `41168580187`, so no new build was started locally. The current
regression repair is **CI pending**. No local full-project Lean build.

**Still unproved / unpaid.** No new theorem is paid. `EdgeValid`, `SectorValid`,
strict canonical total, `Q0Degree3AreaInput`, all seven exclusions, and the
arbitrary-centre theorem remain unpaid.

**Next concrete step.** After supervisor commit, require CI exit 0 for
`SevenClassQ0Deg3EndpointChecks`, then `UpperReductionUnimodal`; use the first
unblocked error.

## 2026-10-31 (session 95) -- explicit CI target for table constants

**Did.** Added `SevenClassQ0Deg3UpperTables` directly to lane-A `TARGETS.txt`;
it previously entered CI only transitively.  The Session 81 relabelled bridge
was already listed and was left unchanged.

**Checks (scope).** Target-list inspection only; no Lean build was run locally.
No source bytes changed and no theorem became paid.

**Still unpaid.** Endpoint repair, `EdgeValid`/`SectorValid`, canonical strict
finite total, relabelled certificate, `Q0Degree3AreaInput`, all seven exclusions,
and the arbitrary-centre theorem.

**Next concrete step.** After supervisor commit, inspect CI in dependency order;
fix the first error in `EndpointChecks`, then the sector/table chain.
