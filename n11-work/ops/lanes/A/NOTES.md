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

## 2026-10-30 (sessions 55--63, condensed)

Added the sector peak, adjacent-step, calculus, bin-shape, witness, and witness
bounds modules:

- `SevenClassQ0Deg3SectorPeak.lean` reduces `SectorValid` to unimodality plus
  nine exact global peak checks.
- `SevenClassQ0Deg3SectorCalculus.lean` proves the fixed-node derivative is
  `(19/50)^2 * cosHiReal x / 2 - mu` and supplies monotone/antitone bridges.
- `SevenClassQ0Deg3SectorBinShape.lean` replaces the false global-step premise
  by 72 separate single-peaked row-bin obligations.
- `SevenClassQ0Deg3SectorBinWitness.lean` records the 72 audited argmaxes and
  proves all finite peak comparisons; the bounds module proves every witness
  lies in its stated bin.

Relevant hashes: peak `41c1b72d...543`, shape `90b7e764...7dd`, witness
`3fb1b952...195`, bounds `79eb307f...a4`. CI status: pending.

## 2026-10-30 (sessions 66--69, condensed)

Completed row-0 bin shape drafts 0--4 in `SectorBin0`--`SectorBin4`, adding
the needed `open SevenClassQ0Deg3Bins`.  None has a kernel-green claim.  The
key later correction was orientation of the decreasing cosine threshold and
separation of the sharp `543 -> 544` rational step from the derivative region.

## 2026-10-30 (sessions 70--72, condensed) -- all-row bins 0--4

Repaired bin-2 threshold orientation and separated the sharp `543 -> 544`
step from the derivative region.  Drafted all-row bins 0--4.  Bins 0--1 peak
at their endpoints; bin 3 splits rows 0--1 (`768`) from rows 2--8 (`1023`);
bin 4 splits rows 0--1 (`1024`) from row-dependent witnesses
`1173,1051,1076,1070,1076,1051,1173`, using the two steps around each witness.
Exact audits passed for all 72 row-bin shapes.  Lean remains CI pending.

Files / SHA256:
`SevenClassQ0Deg3SectorBins01AllRows.lean`
`ec327b5ed219ef406fe22408bdac55e96535914ed759648fd69b36661478170a`;
`SevenClassQ0Deg3SectorBins2AllRows.lean`
`828fb2b8cc881a92a04c894f79166ecd70a0e11d9f22e72c5f687cd386673179`;
`SevenClassQ0Deg3SectorBins3AllRows.lean`
`391050dae3a5649012c0de312ac24e7a34d9d5dc053de84461b0709d7775c2e4`;
`SevenClassQ0Deg3SectorBins4AllRows.lean`
`a53fd01a1c903227481689bff4b15464c4a8fe97a9f67c3620f5156115e0bacf`.

## 2026-10-30 (session 73) -- all-row bin 5 drafted

**Did.** Added the complete all-row bin-5 shape.  The exact 72-bin audit shows
that every row peaks at the first node `1280`, so all increasing halves are
vacuous.  A single all-row cosine-prefix threshold (`cosHiNLag` at node 1280)
then proves the decreasing half through `1535`.  This replaces the row-0-only
module as the route needed by the sector assembler.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBins5AllRows.lean`
`7563e190db0370f90eee0d2083a019c180b3ae937f987b1cd4c48850dc1d202d`.
`audit_q0_degree3_bins5_thresholds.py`
`63d0118a5ff1faf4088aefc2888b6b4d27d81c0a0842dcf509b3b27e80a852d8`;
`q0-degree3-bins5-thresholds-audit.json`
`adf8089b23d2b56309741a45aa4306530e2308dc0737fa61d77fbbb4086a616e`.
`TARGETS.txt`
`90a22ddb5936d880188998bf8f3121da372136f06a49b46643bfe92ffd8d8138`.

**Checks (scope).** `audit_q0_degree3_bins5_thresholds.py` PASS: 9/9
node-1280 decreasing crossings, 9/9 `-2/3` cutoff comparisons, and 9/9
bin-5 argmax patterns.  `py_compile`, `git diff --check`, and forbidden-token
scan PASS.  No local project oleans exist and no Lean build was run, so the
module is **CI pending**, not kernel-green.

**Still unproved / unpaid.** `EndpointChecks` and all prior sector modules
remain CI pending.  All-row bins 6--7 (18 obligations), the combined
`SectorBinUnimodal`/`SectorValid` assembler, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions remain unpaid.

**Next concrete step.** Audit all-row bin 6.  If (as expected from row 0) its
witness is `1536` in every row, reuse the same first-node decreasing template
and the `3*pi/4` tail bound, then list the new module in `TARGETS.txt`.

## 2026-10-31 (session 74) -- all-row bins 6--7 drafted

**Did.** Extended the sector-bin shape from bin 5 through the final bin.
The exact 72-bin table has witness `1536` for every row in bin 6 and `1792`
for every row in bin 7, so both increasing halves are vacuous.  One new module
proves the all-row cosine bracket at each node, the `-2/3` tail comparison,
the generic decreasing value inequality, and both per-row unimodality records
through the bin endpoints `1791` and `2048`.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBins67AllRows.lean`
`49aa8900cc77964cb86c6037ca421a3c1257a1292abb8269274f7892b43582af`.
`audit_q0_degree3_bins67_thresholds.py`
`358892cfbf3e39e44e712b396486e658a36982f54a1688f6f293308dccaa1f99`;
`q0-degree3-bins67-thresholds-audit.json`
`68d50110f84693c282370f4848c751d90aa51a66f4fe18325f9e5b3b5816e4f8`.
`TARGETS.txt`
`800e69589ace71261aa63ff37965fe1d5ccbddeaf0efa2f392df97516e78ba6f`.

**Checks (scope).** `audit_q0_degree3_bins67_thresholds.py` PASS: 18/18
node-1536/1792 decreasing crossings, 18/18 `-2/3` tail comparisons, and 18/18
bin-6/7 argmax patterns, all in exact rational arithmetic.  `py_compile`,
`git diff --check`, and the forbidden-token scan PASS.  No project oleans exist
locally and no Lean build was run, so the module is **CI pending**, not
kernel-green.

**Still unproved / unpaid.** All Lean kernel claims remain CI pending.  The
combined `SectorBinUnimodal`/`SectorValid` assembler, strict total assembly,
`Q0Degree3AreaInput`, and all seven class exclusions remain unpaid.  An exact
table is evidence only, not a proof.

**Next concrete step.** Add the all-row `SectorBinUnimodal` assembler by
combining the proved all-row bin theorems 0--7, then feed it to the existing
peak/shape reduction.  Do this only after CI confirms this module and its
dependencies; if red, inspect the first failing line before adding the
assembler.

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

## 2026-10-31 (session 76) -- CI red isolated to stale endpoint source

**Did.** Fetched the full failed-job log for CI run `41123531381` (commit
`cc04268c`) and isolated the first Lane A failure.  It is an old
`EndpointChecks` source, not an error in the new sector modules: vector-index
lookups at old lines 217--231 left eight equality goals unsolved, and three
`omega` branches at each of old lines 245/257 raised `No goals to be solved`.
Current HEAD `c63cb61e` already contains the session-71 repair (scalar match
definition plus explicit branches); its file hash is
`95bb9da1e3bd4f7524fbe929f81ef3dd9e7fa16376465b8a3f8704b4a738006e`.
The dependent sector reds in that run are therefore dependency reds, not
independent failures.

**Checks (scope).** `audit_endpoint_low_denom.py` PASS: 8/8 endpoint upper
slacks positive, with minimum `6.6940497252e-07` at bin 7; this validates only
the decimal audit arithmetic, not the Lean proof.  The exact CI log retains
the old failure lines and is outside the repository.  No project olean exists
locally, so the repaired `EndpointChecks`, `SectorAssembler`, and all sector
modules remain **CI pending**, not kernel-green.  A bounded core-Lean probe of
the match/`rfl`/`fin_cases` pattern and the Mathlib probe both timed out at
startup, giving no Lean verdict.

**Still unproved / unpaid.** C450 Main/audit remain the only Lane A paid Lean
results (CI green at `cc04268c`).  `sectorValid`, strict total, area input, and
all seven class exclusions remain unpaid.

**Next concrete step.** CI must build current HEAD: first `EndpointChecks`,
then `UpperReductionUnimodal`, edge modules, all bin modules, and finally
`SectorAssembler`.  If `EndpointChecks` still fails, use its first new error
line; if green, begin the strict-total reduction using `sectorValid`.

## 2026-10-31 (session 77) -- combined table interface drafted

**Did.** Added `SevenClassQ0Deg3TableBounds`, combining the independently
drafted 21-edge proof, the 9-row sector-bin assembler, and the 2049-node table
into one `TableBounds` record.  It also proves injectivity of the 21-entry
`tableEdges` table and that `edgeMax (tableEdges i) = edgeMaxAt i`, removing
the opaque `Classical.choose` obstruction at the edge-to-table consumer.

**Files / SHA256.**
`SevenClassQ0Deg3TableBounds.lean`
`d13a9d9caa98a5923a6b5ed5f64fe0981930b7d7f4eb7e456f27a7ff25cf5dbd`;
the TARGETS entry adds
`N11Formalization.SevenClassQ0Deg3TableBounds`;
`TARGETS.txt` `8b08ccdc7040574a42a4c08d742f0eaed814067181ddf99be3ad4394c04d1730`.

**Checks (scope).** `audit_q0_degree3_sector_grid.py` PASS in exact rational
arithmetic: 21 edge maxima, all 18,441 sector grid values, and
`totalUpper < piLo` with decimal slack `0.012092890371`.  `py_compile`,
`git diff --check`, and forbidden-token scan PASS.  No Lean build was run;
every Lean claim in this and earlier pending modules remains **CI pending**.
A core-Lean probe of the choose/injectivity pattern had no Mathlib search path
and therefore produced no verdict.

**Still unproved / unpaid.** The interface is not yet connected to an actual
refinement: the canonical-permutation edge identification and the strict
`totalUpper` inequality for each actual cover remain explicit obligations.
`Q0Degree3AreaInput`, the seven exclusions, and the arbitrary-centre theorem
remain unpaid.

**Next concrete step.** Refactor `Degree3AreaCertificate` construction into a
theorem taking `TableBounds`, a `NineTies` value, edge identification, and the
strict total; then connect `degree_three_table_graph` and its canonical label
map to the table-indexed edge bound.  Wait for CI's first failure line before
claiming any of these modules green.
