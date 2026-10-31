EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 124): frozen-piHi peak/table repairs are complete in the
worktree but remain uncommitted; the exact-byte kernel build is CI pending.

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

## Earlier sessions (24--104, condensed)

Repaired the C450 chain, Cos/Mono/Bins, endpoint checks, edge peaks/suffixes,
sector calculus/bins/assembler, table and relabelled-certificate chain. Exact
72-bin/grid audits passed, but no Lean target was credited by arithmetic.

## 2026-10-31 (sessions 86--114, condensed)

Repaired endpoint branches/imports, added the strict-total emitter/module
(total `3.129499763218794...`, slack `0.012092890370999...`), replaced the
global sector-step premise with certified fixed-bin maxima, and normalized both
peak wrappers. Exact audits passed but none of these outputs is proof credit;
all remain **CI pending**.

## 2026-10-31 (sessions 115--117, condensed)

Replayed the exact edge derivative/unimodal and sector grid audits (21 edge peaks,
21 discrete peaks, 18,441 sector points; strict-total slack
`0.012092890370999008`). Repaired edge 1/8 endpoint comparisons at node 877;
all 10 literal checks, two endpoint steps, and helper declaration order pass.
Added folds/unfolds required by CI and corrected the maintained CI interpretation.
These remain source/arithmetic checks, not kernel credit; `degree_three_table_graph`
still has a `sorryAx` dependency.

## 2026-10-31 (session 118) -- sector peak symbolic-site owner

Run `41217409382` completed on `068914fb`. Its first independent lane-A owners
were all 21 edge peaks and all 9 sector peaks (`unsolved goals`), not rational
falsehoods. In the sector goals `norm_num` left
`ActualRingDirectionOrder.ringSite (ActualBoundaryCyclicOrder.nextRing i)`
symbolic; the green bin modules already included `ringSite, nextRing` for this
reason. Added both names to every sector peak simp set and its emitter; extended
the textual gate to require them. The committed edge-prefix fix replaces the
opaque `Finset.sum` `edgeCoeff` with exact literals and is included in the later
`8f861bae` build, but that build predates this sector edit.

**Files / SHA256.** `SevenClassQ0Deg3SectorPeak.lean`
`901e59b7ef79eabf9a69735696d49ff7876d0eac3df86b02dc9ffffdb5760cb3`;
`emit_q0_degree3_sector_peak.py`
`98fa8678145e3f6a6401a7097989295617d4e9e829928a7e3baa1ca47e5a613e`;
`check_q0_degree3_sector_peak_unfold.py`
`886123c4cbac09adf37ad31cfc6497af69add8a7b7964cf2a9c4e155157105bd`.

**Checks (scope).** CI log owner diagnosis at `068914fb`; deterministic emitter
regeneration produced the listed Lean hash; sector gate PASS 9/9;
`py_compile` and `git diff --check` PASS. No local project kernel build, so the
repair is **CI pending**. Run `41222715534` was still in progress on `8f861bae`.

**Still unproved / unpaid.** Kernel acceptance of both peaks, suffixes,
`EdgeShape`, sector shape/calculus/bins, table/strict-total, and
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-centre theorem.

**Next concrete step.** On the next committed build, inspect the separate
`UpperReductionUnimodal`, `SectorPeak`, then `EdgeSuffixNonpos`/`EdgeShape`
exits. If sector peaks are green, take the first independent `EdgeShape` error;
do not diagnose dependency-red bins/table targets.

## 2026-10-31 (session 119) -- explicit sector boundary label

Live run `41222715534`, job `124600429120`, at `8f861bae` built
`SevenClassQ0Deg3SectorPeak` and exposed all nine first goals.  The prior
`unfold`/simp-list repair was insufficient: each goal retained the opaque index
`ringSite (nextRing i)`.  The emitter now rewrites `nextSite i` to the exact
boundary label `(i+1) mod 9` before `norm_num`.  The same rewrite was propagated
to all 72 `sectorBinPeakValid_*` checks, which would otherwise inherit the defect.

**Files / SHA256.** `SevenClassQ0Deg3SectorPeak.lean`
`f004ad499c0926ba924035323cd66c452b7deb2a633994fe35ff2ab480d31ae1`;
`SevenClassQ0Deg3SectorBinWitness.lean`
`d38aeb93cb7e98613221be6faea23060af6e16fdbc81c3893ed004bbb4401549`;
`emit_q0_degree3_sector_peak.py`
`6f2f9a9a4cfbe2bd90cd7297e37e3ac63e043f9ac4ea08fb74d212bf125fd87e`;
`emit_q0_degree3_sector_bin_witness.py`
`45cc76782b330a6d56906947eedde3719002d9fdea335f561a2a2c7bc4db4566`.

**Checks (scope).** CI first-goal diagnosis at `8f861bae`; deterministic emitter
regeneration PASS; sector/edge textual gates PASS 9/9 and 21/21; all 72 bin
witnesses contain the explicit label rewrite; edge-literal audit PASS 10/10 + 2/2;
`py_compile` and `git diff --check` PASS.  No project Lean kernel build ran
locally, so this repair is **CI pending**, not proof credit.

**Still unproved / unpaid.** Kernel acceptance of peaks and bin witnesses;
suffixes, `EdgeShape`, sector calculus/bins, table/strict-total, and
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-centre theorem.

**Next concrete step.** On the committed run, inspect `SectorPeak` first.  If
green, take the first independent `SectorBinWitness` goal; do not diagnose
dependency-red downstream modules.

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

## 2026-10-31 (session 123) -- deterministic regeneration and CI scope

Re-ran both session-122 emitters.  They regenerated byte-identical Lean:
upper tables `dcad2b97889dedfca205799add1d0657b4f5239a5f70362d5372da4df69c62bd`;
sector peak
`d6afaaee9257d12304107f6708366829ca09f24a810af8a87c071557554b4bda`.
The edge and sector textual unfold gates both PASS (21/21 and 9/9).

Run `41229638083` (job `124624464765`) started 18:43 UTC and is still
`in_progress`.  It is on `9031cec3`: `git show` confirms that commit still has
the pre-repair sector hash `f004ad49...d31ae1` and pre-repair upper-table hash
`e18374ec...88a9`, so this run **cannot validate the session-122 bytes**.
No local project kernel build ran; the repair remains **CI pending**.

**Still unproved / unpaid.** Unchanged: kernel acceptance of peaks and bins,
then sector shape/calculus/bins, table/strict-total, `Q0Degree3AreaInput`,
all seven exclusions, and the arbitrary-centre theorem.

**Next concrete step.** Once the supervisor commits the current worktree,
read the new run's first independent `UpperReductionUnimodal`/`SectorPeak`
red.  If both build, diagnose the first independent `SectorShape` goal; ignore
dependency-red downstream modules.

## 2026-10-31 (session 124) -- exact-byte commit/CI scope audit

Confirmed the session-122 repairs are still uncommitted.  Supervisor commit
`9ce84728` contains the old sector/upper-table bytes
(`f004ad49...d31ae1`, `e18374ec...88a9`), so CI on it cannot validate them.
The current worktree hashes remain upper tables
`dcad2b97889dedfca205799add1d0657b4f5239a5f70362d5372da4df69c62bd`,
sector peak
`d6afaaee9257d12304107f6708366829ca09f24a810af8a87c071557554b4bda`,
and upper reduction
`0cad77f31891bf9401cba9fdc701f29bb990cc52dd7ef770550522b96780c135`.
`git diff --check`, `py_compile` of both emitters, and the 9/9 sector textual
unfold gate pass.  Scope is source/text/arithmetic only; no local kernel build.

**Still unproved / unpaid.** Kernel acceptance of the repaired peaks and bins,
then suffixes/`EdgeShape`, sector calculus/bins, table/strict-total,
`Q0Degree3AreaInput`, all seven exclusions, and the arbitrary-centre theorem.

**Next concrete step.** After the supervisor commits the current worktree,
inspect the new `n11-lean-build` run's first independent
`UpperReductionUnimodal` and `SectorPeak` errors.  If green, take the first
independent `SectorBinWitness` error; ignore dependency-red descendants.

## 2026-10-31 (session 125) -- CI scope (condensed)

Run `41229638083` remains in progress on old `9031cec3`; commit `9ce84728`
also predates the repairs.  API/hash/ancestry checks only, no kernel build.

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
