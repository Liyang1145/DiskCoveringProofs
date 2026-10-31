EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 131): the maintained sector-grid audit now uses Lean's
`nextSite` pairing.  No lane-A kernel verdict exists yet.

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

## 2026-10-31 (sessions 115--117, condensed)

Replayed the exact edge derivative/unimodal and sector grid audits (21 edge peaks,
21 discrete peaks, 18,441 sector points; strict-total slack
`0.012092890370999008`). Repaired edge 1/8 endpoint comparisons at node 877;
all 10 literal checks, two endpoint steps, and helper declaration order pass.
Added folds/unfolds required by CI and corrected the maintained CI interpretation.
These remain source/arithmetic checks, not kernel credit; `degree_three_table_graph`
still has a `sorryAx` dependency.

## 2026-10-31 (sessions 118--119, condensed)

CI owners were all 21 edge peaks and nine sector peaks, initially because
`ringSite`/`nextRing` stayed symbolic.  The emitters/Lean now unfold those
namespaces and rewrite `nextSite i` to `(i+1) mod 9`, including all 72 bin
witnesses.  Textual gates passed, but no corresponding kernel verdict arrived.

## 2026-10-31 (sessions 120--121, condensed) -- reachable bin index

All 72 emitted bin proofs unfold `sectorAt sectorValue` before rewriting
`nextSite` to `(i+1) mod 9`.  The bin audit passed 72/72 witnesses, 18,369
within-bin steps, and 63/63 inter-bin jumps; the peak gate passed 9/9.
A bounded Mathlib probe timed out and is not evidence.  Still **CI pending**.

## 2026-10-31 (session 122) -- frozen-piHi maxima and namespace repair

Live CI on `9031cec3` exposed two independent lane-A defects.  `SectorPeak`
could not elaborate `ringSite`/`nextRing` because their defining namespaces
were not opened.  More substantively, all edge/sector maxima came from the
source JSON's upper `piHi`, which is slightly below the frozen Lean
`RatInterval.piHi`; the 21 edge peaks therefore reduced to `False` rational
goals, and the sector table also paired `mu i` with Lean's `mu (nextSite i)`.
The upper-reduction composition additionally omitted `unfold EdgeCheck`.

The upper-table and sector-peak emitters now recompute exact maxima at the
frozen Lean rational, use `mu ((site+1) mod 9)` for sectors, and emit the
correct sector witnesses `[1024,1536,1536,1536,1536,1536,1536,1536,1024]`.
`SectorPeak` opens `ActualRingDirectionOrder` and
`ActualBoundaryCyclicOrder`; `edgeValid_of_unimodal` unfolds `EdgeCheck`.

**Files / SHA256.** `SevenClassQ0Deg3UpperTables.lean`
`dcad2b97889dedfca205799add1d0657b4f5239a5f70362d5372da4df69c62bd`;
`SevenClassQ0Deg3SectorPeak.lean`
`d6afaaee9257d12304107f6708366829ca09f24a810af8a87c071557554b4bda`;
`SevenClassQ0Deg3UpperReductionUnimodal.lean`
`0cad77f31891bf9401cba9fdc701f29bb990cc52dd7ef770550522b96780c135`;
`emit_q0_degree3_upper_tables.py`
`f016b44b361a1ea3cc0e54744f34e469b4689494f236d8146f8cbd3484693b74`;
`emit_q0_degree3_sector_peak.py`
`badf2f26dee1acdb514ac648375def9d6788c805a49f4eca6918eb7737cab709`.

**Checks (scope).** Exact regeneration PASS for 21 edge maxima/witnesses and
9 sector maxima; 9/9 six-decimal sector bounds enclose their exact Lean-piHi
maxima by less than `1e-6`; textual sector gate PASS 9/9; edge gate PASS
21/21; `py_compile` and `git diff --check` PASS.  These are source and
exact-rational checks only.  No local project kernel build ran, so the repair
is **CI pending**, not proof credit.

**Still unproved / unpaid.** Kernel acceptance of edge/sector peaks, their
shape/calculus/bin descendants, table/strict-total, `Q0Degree3AreaInput`, all
seven exclusions, and the arbitrary-centre theorem.

**Next concrete step.** On the next committed CI run, inspect
`UpperReductionUnimodal` first: its peak checks now target exact Lean-piHi
maxima and its composition unfolds `EdgeCheck`.  Then inspect `SectorPeak`;
do not diagnose dependency-red suffixes/bins/certificates.

## 2026-10-31 (session 126) -- emitter/Lean witness mismatch repaired

Static comparison found the session-122 Lean still declared
`sectorWitness = [1024,1024,1536,...]` while `sectorPeakValid_1` rewrote index
1 to `1536`; that `decide +kernel` could not succeed.  The emitter now renders
the computed witness vector instead of hard-coding it, and regeneration gives
the correct `[1024,1536,1536,1536,1536,1536,1536,1536,1024]`.

**Files / SHA256.** `SevenClassQ0Deg3SectorPeak.lean`
`2a95b7a34aa8ec11acdf10f83116b586ca6380deef4447ab8033daf02ca5ca11`;
`emit_q0_degree3_sector_peak.py`
`a0e32e4a00585e772b39261c0015ec01d2f1294cc3bf11b7f8fd6e0cc7e2036c`.
Upper tables remain `dcad2b97...c62bd`; upper reduction remains
`0cad77f3...0c135`.  **Checks (scope):** deterministic emitter regeneration,
9/9 sector textual unfold gate, `py_compile`, and `git diff --check` PASS.
No project kernel build ran; **CI pending**.

**Still unproved / unpaid.** Kernel acceptance of peaks/bins, then sector shape,
calculus and certificates; `Q0Degree3AreaInput`, all seven exclusions, and the
arbitrary-centre theorem.  **Next:** commit these bytes, then diagnose the first
independent `UpperReductionUnimodal`/`SectorPeak` error on the new SHA.

## 2026-10-31 (session 127) -- strict-total ledger repaired

Repaired `verify_q0_degree3_strict_total.py` (SHA256
`a355027601f45612f3fbf64d1265d34a21c20808567ec0b53d954c01e40f493f`).
It had compared Lean's shifted, Lean-`piHi` sector table against the 40-digit
manifest table.  Each ledger now uses its own maxima, `mu`, `lam`, and `pi` pair.

**Checks (scope):** verifier PASS: Lean total `3.129499763218794`, slack
`0.012092890370999`; manifest delta `5.506e-21`; exact edge audit PASS 21/21;
edge/sector textual unfold gates PASS; `py_compile` and `git diff --check` PASS.
These are arithmetic/text checks, not kernel credit.  CI run `41235435914` was
still in its Lean build step at 19:55 UTC; a local probe of the two generic
adjacent-step lemmas exceeded the 90 s import cap, so no local kernel result.

**Unpaid:** unchanged: kernel peaks/edge/sector shape, `Q0Degree3AreaInput`,
seven exclusions, arbitrary-centre theorem.  **Next:** on the completed job,
diagnose the first independent `UpperReductionUnimodal`/`SectorPeak` error.

## 2026-10-31 (session 129) -- stale-owner diagnosis and byte verification

Downloaded the live log for `41237352391` and the completed log for
`41229638083` (`9031cec3`).  The latter is the first build that reached lane A:
C450/Main/Audit, Cos, Mono, Bins, EndpointChecks and UpperTables were green;
UpperReductionUnimodal and SectorPeak were red, with all descendants
dependency-red.  Its two owning defects were (a) `edgeValid_of_unimodal`
returned the unfolded bound instead of `EdgeCheck i k`, and (b) sector peak
proofs referenced `ringSite`/`nextRing` without the two defining namespaces,
leaving each rewritten goal unsolved.  It also predates the corrected
`edgeMaxAt` table.  The current `d8893a1b` bytes already repair (a) with
`unfold EdgeCheck`, (b) with both namespace opens, and the table bytes.

**Files / SHA256.** `SevenClassQ0Deg3SectorPeak.lean`
`2a95b7a34aa8ec11acdf10f83116b586ca6380deef4447ab8033daf02ca5ca11`;
`SevenClassQ0Deg3UpperReductionUnimodal.lean`
`0cad77f31891bf9401cba9fdc701f29bb990cc52dd7ef770550522b96780c135`;
`SevenClassQ0Deg3UpperTables.lean`
`dcad2b97889dedfca205799add1d0657b4f5239a5f70362d5372da4df69c62bd`.

**Checks (scope).** Read-only live/completed CI log extraction; textual unfold
gates PASS 9/9 and 21/21; exact edge-literal audit PASS 10/10 + 2/2; the two
peak emitters `py_compile` PASS; `git diff --check` PASS.  These establish only
that the stale owners are addressed in source, not kernel acceptance.  Run
`41237352391` remains **in progress in lane B**; peaks are **CI pending**.

**Still unproved / unpaid.** Kernel acceptance of both peaks, edge/sector shape
and bins, table/strict-total, `Q0Degree3AreaInput`, all seven exclusions, and
the arbitrary-centre theorem.

**Next concrete step.** When `41237352391` reaches lane A, parse its
`=== EXIT` lines and read the first independent UpperReductionUnimodal or
SectorPeak error; do not diagnose dependency-red suffix/bin targets.

## 2026-10-31 (session 130) -- Lean sector pairing audited

Run `41237352391` (`bb9fb0c0`) remained `in_progress` in lane B at 20:41 UTC;
no lane-A kernel verdict is available.  Independent exact-rational recomputation
confirmed all nine emitted sector witnesses under the actual Lean pairing
`mu (nextSite i) = mu ((i+1) mod 9)`: witnesses
`[1024,1536,1536,1536,1536,1536,1536,1536,1024]`, each attaining its row maximum
exactly.  The old grid audit still uses report row `mu i`; its reported maxima
and strict total agree as a multiset/sum, but its row witnesses are stale.  No
Lean source needed changing.

**Checks (scope).** Independent Python `Fraction` replay of 9 x 2049 sector
values at frozen Lean `piHi`; exact witness-to-max equality 9/9.  Existing
sector/edge textual gates PASS 9/9 and 21/21; strict-total verifier PASS (slack
`0.012092890370999`); 21-edge + 9-sector grid arithmetic PASS; `py_compile` and
`git diff --check` PASS.  These are arithmetic/text checks, not kernel credit.

**Still unproved / unpaid.** Kernel acceptance of both peaks and all descendants;
shape/calculus/bins, `Q0Degree3AreaInput`, seven exclusions, arbitrary-centre
theorem.

**Next concrete step.** When `41237352391` reaches lane A, inspect the first
independent `UpperReductionUnimodal`/`SectorPeak` error.  Separately update
`audit_q0_degree3_sector_grid.py` to compute `mu ((site+1) mod 9)` rows and emit
the recomputed witnesses.

## 2026-10-31 (session 131) -- audit aligned with Lean sector pairing

Updated `audit_q0_degree3_sector_grid.py` to compute each sector at
`mu ((i+1) mod 9)`, select each row's exact maximizer, and use that Lean-site
index in the total's `abs(mu ...)` term.  The old report is indexed by `mu i`;
the script explicitly maps source row `(i+1) mod 9` to Lean site `i`.  The
recomputed witnesses are `[1024,1536,1536,1536,1536,1536,1536,1536,1024]`.

**Files / SHA256.** `audit_q0_degree3_sector_grid.py`
`9c6dd64e6ec328e94e7c4b1e028ff05581060820e248d7375fba0e1c10fbc02a`;
`q0-degree3-sector-grid-audit.json`
`f5a2b82dc75d18af5c322b488f43384217b5c11f6a238d7c962bfe8a4a898f43`.
Peak emitter and Lean remain `a0e32e4a...2036c` and `2a95b7a3...ca11`.

**Checks (scope).** Exact-rational audit PASS: 21/21 edge maxima, 9/9 x 2049
sector rows, unchanged strict total `3.129499763218794...`, slack
`0.012092890370999008`; `py_compile` and `git diff --check` PASS.  This is
arithmetic/text evidence, not kernel credit.

**Still unproved / unpaid.** Peak and descendant kernel acceptance, sector
shape/calculus/bins, `Q0Degree3AreaInput`, seven exclusions, and the
arbitrary-centre theorem.

**Next concrete step.** On the next completed lane-A CI job, inspect the first
independent `UpperReductionUnimodal`/`SectorPeak` error; do not diagnose
dependency-red descendants.
