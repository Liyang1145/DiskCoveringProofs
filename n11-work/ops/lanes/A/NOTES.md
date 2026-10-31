EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 116, part 3): repaired an `EdgeShape` declaration-order defect;
the peak-unfold and endpoint repairs remain CI pending.

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

## 2026-10-31 (sessions 110--112, condensed) -- peak normalization

Peak proofs were diagnostic-red at their witness rewrite: the
`EdgePeakValid`/`SectorPeakValid` wrappers were still folded. Earlier repairs
normalized `Fin` coercions, removed the re-unfolding `edgeWitness` from simp
sets, and retargeted sector peaks from rounded `sectorPeakAt` to `sectorMax`.
Historical hashes are in git history.

## 2026-10-31 (session 114, condensed)

The maintained artifact was still the pre-session-112 tree, so its peak exits
were not a verdict on the dirty repairs.  No Lean or arithmetic check ran.

## 2026-10-31 (session 115) -- exact CI peak-error repair

Fetched run `41212560053` job `124570425838` at committed HEAD `66bf2541`. It
is the first run on session-112's peak repairs. Both peak modules fail at their
first proof line, not in rational evaluation: `rw [show edgeWitness i = ...]`
and `rw [show sectorWitness i = ...]` cannot see the witness because
`EdgePeakValid i` / `SectorPeakValid i` is still folded. CI reports this at all
21 and all 9 proofs respectively. C450 completion is unaffected.

Inserted `unfold EdgePeakValid` / `unfold SectorPeakValid` before every witness
`rw`. Synced the sector Python emitter and strengthened both textual gates to
reject a witness rewrite that precedes the unfold.

**Files / SHA256.** `SevenClassQ0Deg3UpperReductionUnimodal.lean`
`9eaeed71f2a47c76d68933e43a975603eaa36c4e6078df5f0dd3199ba8a89a44`;
`SevenClassQ0Deg3SectorPeak.lean`
`be48fee6330a2be99bab6a9008786860bcd1d313fd2335dfed0fc2925eaf4328`;
sector emitter `b0cca7364e6f06a5777a8e3d717f7f3725262ed9c7b6ae2ab73aa20ca29128ed`;
edge gate `af4434a75c38f0f2ef146f9d0cde5aabf3bc00eb7ef0e4eb8b2927782e5e40f2`;
sector gate `93fe300e7ca76b8308ecca02097d3268a173dc07047e5d023e25230d0135db7a`.

**Checks (scope).** CI log diagnosis above; updated edge/sector gates PASS
21/21 and 9/9; emitter `py_compile`, deterministic regeneration (identical
SHA256), and `git diff --check` PASS. A tiny standalone Lean tactic-order probe
timed out under host load and proves nothing. No project kernel build ran
locally, so this repair remains **CI pending**.

**Still unproved / unpaid.** Kernel acceptance of both peaks; edge/sector shape;
bins/assembler/table/strict-total; `Q0Degree3AreaInput`; seven exclusions; and the
arbitrary-centre theorem.

**Next concrete step.** After supervisor commit, inspect the next run's exits.
If either peak still fails, use the new first goal; otherwise take the first
owner error in `EdgeSuffixNonpos`/`SectorShape` from a serial lane build.

## 2026-10-31 (session 116) -- false edge-prefix endpoints repaired

The live instance of run `41212560053` still shows only the pre-unfold peak
errors already diagnosed in session 115; it is not a new regression.  An exact
audit of every `edge_ratio_*_lt_cosT14_nodeQ_*` literal in `EdgeShape` found that
edges 1 and 8 were false at peak node 878: ratios `0.2226682825...` and
`0.2226718144...` versus `cosTQ14 = 0.2220936210...`.  At node 877 both are
strict (`0.2235890292...`), so `edgeIncTo_one`/`_eight` now use
`edgeIncTo_of_monotoneOn_to_prev_and_step 1/8 878 877`, a monotone endpoint at
877, and an explicit exact 877->878 step.  The other eight literal comparisons
were already true.

**Files / SHA256.** `SevenClassQ0Deg3EdgeShape.lean`
`dfe4948bd211cb035dbcd98ceaadef55f0539f7eacdb2815c77fd0babbc9e81c`;
`audit_q0_degree3_edge_literals.py`
`4b7cd62cfc2f9e39acedf68c0a8308a3047d76fad34f38abfd4c0d0264b2c686`;
`q0-degree3-edge-literals-audit.json`
`21fc913121dc77bc67cf875a19ee77dfcdeab4eb9eae85b4399ac027c0e5d8f5`.

**Checks (scope).** Exact source-bound audit PASS 10/10; edge/sector peak-order
gates PASS 21/21 and 9/9; `py_compile` and `git diff --check` PASS.  A 90-second
Mathlib probe of the tactic order timed out and proves nothing.  No project
Lean build ran locally, so `EdgeShape` is **CI pending**.

**Still unproved / unpaid.** Kernel acceptance of both peaks and `EdgeShape`;
`EdgeSuffixNonpos`/sector shape/calculus/bins; table/strict-total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-centre theorem.

**Next concrete step.** After the next commit/run, check `EdgeShape`'s first
owner.  Also exact-check the new 877->878 steps against the term structure if the
sole error is in either `norm_num` step.

## 2026-10-31 (session 116, part 2) -- endpoint-step audit

CI run `41212560053` was before the dirty repairs. Its first independent
owners were the folded peak witness rewrites; later edge targets were dependency-red.
The audit now evaluates the exact 877->878 `edgeUpper` steps for edges 1 and 8
(gaps `3.833978588912...e-8`, `3.755745568730...e-8`) as well as all literals.

**Files / SHA256.** `audit_q0_degree3_edge_literals.py`
`6f2a52bd4c75c39841ba6b5917b5b4da05cc43815e60b2e3db244f55f7d2a638`;
`q0-degree3-edge-literals-audit.json`
`70179d07f80ed0fd30a1dac418a37eedef5e80b6c02d314d7824d90429ea0d62`.
The dirty peak/edge Lean hashes are unchanged from the session-115/116 entries.

**Checks (scope).** Exact source-bound audit PASS 10/10 literals and 2/2 steps;
edge/sector peak-order gates PASS 21/21 and 9/9; `py_compile` and
`git diff --check` PASS.  No local project Lean build ran, so the dirty repairs
remain **CI pending**.

**Still unproved / unpaid.** Kernel acceptance of the peaks and `EdgeShape`;
`EdgeSuffixNonpos`/`EdgeSuffixHigh`, sector shape/calculus/bins, table and
strict-total chain; `Q0Degree3AreaInput`; seven exclusions; arbitrary-centre
theorem.

**Next concrete step.** After the supervisor commits the dirty peak/edge fixes,
inspect the next run's separate peak exits first.  If both peaks are green,
take the first owner in `EdgeSuffixNonpos`/`EdgeSuffixHigh`; do not diagnose
dependency-red descendants.

## 2026-10-31 (session 116, part 3) -- EdgeShape declaration order

Found a concrete owner-level defect: `EdgeShape` used
`edgeIncTo_of_monotoneOn_to` at line 226 and the new
`edgeIncTo_of_monotoneOn_to_prev_and_step` at line 314, but declared them only
at lines 797/834. Lean has no forward theorem references. Moved both generic
helpers once, before their first use; no mathematical statement changed.

**Files / SHA256.** `SevenClassQ0Deg3EdgeShape.lean`
`74a6f4293943e15d2fe6ecd997070b24fe5e3ddb372b3213a4cd666c2f348713`;
`audit_q0_degree3_edge_literals.py`
`8063b5e8fc9755dfdd4af7cb33f613432c04cb1e5a3889bd966563601bf66714`;
`q0-degree3-edge-literals-audit.json`
`c19b505ca420450e017be4a07dbd513b11054e4ce3aace71ef13c298489a5f5b`.

**Checks (scope).** Exact source audit PASS 10/10 literals, 2/2 endpoint steps,
and 2/2 helpers declared before all uses; edge/sector peak gates PASS 21/21 and
9/9; `py_compile` and `git diff --check` PASS. No project Lean build ran locally,
so all dirty Lean repairs remain **CI pending**; this is not proof credit.

**Still unproved / unpaid.** Same as the preceding entry: kernel acceptance of
the peaks/`EdgeShape`; suffix/shape/calculus/bins/table/strict-total chain;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-centre theorem.

**Next concrete step.** After commit, inspect separate peak exits, then the first
owner error in `EdgeShape`. The new helper-order audit is the regression guard.

## 2026-10-31 (session 117) -- corrected CI state and exact replay

The maintained `ops/ci/LATEST.md` was stale. GitHub API shows run
`41212560053` completed at 15:48 on `66bf2541`; the job conclusion is success,
but its summary exits contain the expected folded-wrapper peak reds and all
downstream lane-A targets are dependency-red. It is not Lane-A credit. A new
build `41217409382` is in progress on `068914fb`, which includes the committed
`unfold` and `EdgeShape` repairs.

**Files / SHA256.** No Lean source changed this session. Replayed reports:
`q0-degree3-edge-derivative.json`
`628a20f6e4758b3a18ccd83215ac23a7e2fabbb11c701bd667a820643b97d726`;
`q0-degree3-edge-unimodal.json`
`2a0a38b150cae0b9d200c90f273084b3bdbd4f51d43f4eca1270d8ea5b2f412f`;
`q0-degree3-sector-grid-audit.json`
`bc0dd05c4dd7a38f08ae98d916a1eff5bbe8b7db98bdd53749278049215669b9`.

**Checks (scope).** Exact-rational replay PASS: 21/21 edge derivative signs;
21/21 exact discrete single peaks; 21 edge maxima; all `9 x 2049 = 18,441`
sector points; strict `totalUpper < piLo` with slack
`0.012092890370999008`. Source gates PASS 10/10 edge literals, 2/2 endpoint
steps, 2/2 helper declarations before uses, 47 references across 38 modules,
and 21/21 plus 9/9 peak unfolds. These are arithmetic/source checks, not kernel
credit.

**Still unproved / unpaid.** Kernel acceptance of both peaks, suffixes,
`EdgeShape`, sector shape/calculus/bins, table/strict-total, and
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-centre theorem. The
existing `degree_three_table_graph` axiom report contains `sorryAx`, so it is
also unpaid and must not be treated as class credit.

**Next concrete step.** When `41217409382` finishes, take its first independent
owner among `UpperReductionUnimodal`, `SectorPeak`, then `EdgeShape`; do not
diagnose dependency-red descendants. Do not edit frozen modules to chase the
`sorryAx` dependency.
