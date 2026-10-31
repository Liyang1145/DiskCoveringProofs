EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 118): identified the concrete symbolic `ringSite` defect in all
nine sector peaks; repair is CI pending.

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

## 2026-10-31 (session 120) -- reachable sector-bin index rewrite

The session-119 bin repair rewrote `nextSite i` before unfolding `sectorAt`, so
the occurrence remained hidden inside `sectorValue`.  All 72 emitted proofs now
execute `unfold sectorAt sectorValue` before the kernel-decided `nextSite`
equality; this exposes the single reachable occurrence and preserves the exact
boundary label `(i+1) mod 9`.  The nine global-peak proofs retain their prior
unfold/rewrite order.

**Files / SHA256.** `SevenClassQ0Deg3SectorBinWitness.lean`
`d6578beccb9a06091c29c5328c14ddfa2f0f96f2649c11bc914239fa3591264c`;
`SevenClassQ0Deg3SectorPeak.lean`
`f004ad499c0926ba924035323cd66c452b7deb2a633994fe35ff2ab480d31ae1`;
`emit_q0_degree3_sector_bin_witness.py`
`653364bc8a7b4b81c2b0c3549bea18dbd6595b0673f409283ee1dd856fb37292`;
`emit_q0_degree3_sector_peak.py`
`6f2f9a9a4cfbe2bd90cd7297e37e3ac63e043f9ac4ea08fb74d212bf125fd87e`.

**Checks (scope).** Deterministic regeneration PASS; 72/72 proofs contain the
new unfold; sector-peak textual gate PASS 9/9; exact bin audit PASS 72/72
witnesses, 18,369 within-bin steps (8,724 up / 9,645 down), 63/63 inter-bin
jumps; bin-shape audit PASS 9/9 false global steps and 72/72 single-peaked
restrictions; `py_compile` and `git diff --check` PASS.  These are source and
exact-rational checks only.  No project kernel build ran locally, so both
repairs remain **CI pending**.

**Still unproved / unpaid.** Kernel acceptance of global sector peaks and all
72 bin witnesses; subsequent suffixes/`EdgeShape`, sector calculus/bins,
table/strict-total, `Q0Degree3AreaInput`; all seven exclusions and the
arbitrary-centre theorem.

**Next concrete step.** On the next committed CI run, inspect first independent
failures in this order: `SectorPeak`, then `SectorBinWitness`.  For a red bin,
read its first `sectorBinPeakValid_ij` goal after the new unfold; do not treat
dependency-red downstream modules as diagnostics.

## 2026-10-31 (session 121) -- session-120 gates replayed

Replayed both non-kernel gates after the reachable-index repair.  The sector
peak textual gate passed 9/9 declarations; the exact-rational bin audit passed
72/72 witnesses, 18,369 within-bin steps (8,724 up / 9,645 down), and 63/63
inter-bin jumps.  `py_compile` for both emitters, the peak checker, and the bin
audit passed; `git diff --check` passed.  The bin audit JSON was regenerated
(`60ecd42746aa7fac7bf3010418ebe41fc9169334132293cb55d41cc4f18dbe09`).

An isolated Mathlib-only probe of the exact `unfold sectorAt sectorValue` then
`rw [show nextSite 0 = 1 ...]` tactic pattern was attempted, but Mathlib import
exceeded its bounded 120-second local timeout; it produced no Lean result and
is not evidence.  The source hashes are unchanged from session 120 (peak
`f004ad49...d31ae1`, bins `d6578bec...1264c`).

**Still unproved / unpaid.** Kernel acceptance of the peaks and bins, all later
sector/edge/table/strict-total obligations, `Q0Degree3AreaInput`, all seven
exclusions, and the arbitrary-centre theorem.  No CI run exists yet for these
uncommitted bytes, so status remains **CI pending**.

Live API inspection at session end found no newer `n11-lean-build` run:
`41222715534` (head `8f861bae`) still reported `in_progress`; the newer
`335d6b13` runs were only scoped math replay and delivery checks.  The latter
delivery failure is manifest/byte auditing, not a lane-A Lean diagnostic.

**Next concrete step.** When the supervisor commits these bytes, read the new
CI job's first independent red: inspect `SectorPeak` first, then the first
`SectorBinWitness` theorem.  If both are green, continue with the first
independent `SectorShape`/calculated-bin owner rather than dependency-red
modules.
