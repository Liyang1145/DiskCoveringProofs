EXPERT (2026-11-02):
- Actual energy remains 2013/2386 (373 open). The 389->334 chain is conditional set algebra, not 55 paid ids; do not quote 334/332 as paid.
- Stop adding census links. 232 serial targets cannot reliably reach the tail in the 5-hour CI budget; park 3578/3738 and later links.
- The 334 note overclaims static PASS: there is no committed `verify_census_334.py` or audit JSON. Add that independent exact-complement check.
- Highest leverage: make `EnergyRefineN0038` real, then the wrapper and `ResidualRadiusCertificate 38`; require `new_radius` and `paid_radius` green with clean axioms.
- Removing `maxHeartbeats 0` is not a repair: drafts retain `maxRecDepth 100000` and 12-13 KB rational literals with 13-36 giant `decide +kernel` checks.
- Split each `validN : MValid pkN` by the eight `MValid` fields and packet leaves: `fin_cases` over `Fin 16/36/9/7`, then exact `norm_num` on closed comparisons.
- Gate one id per CI cycle, smallest first (0038), and preserve the first owning error; no further bridge until one id is paid.
- Keep the original root and toolchain untouched; this lane earns energy credit only through the B13 consumer.

# Lane C notes

## Standing constraints

- Kernel credit requires CI exit 0 and a mathematical consumer. Exact rational
  audits, static scans, and hash/tree audits are diagnostics only.
- No `sorry`/`admit`/new `axiom`/`native_decide`/`ofReduceBool`/
  `implemented_by`/`maxHeartbeats 0`; do not edit frozen modules, root,
  lakefile, toolchain, or manifest.
- Preserve green `FrozenCapRationalCore`, `PaidCellCertificateM`,
  `PaidCellCertificateMCap`, and `FrozenCapWideFieldWitnesses` unchanged.
- `ExcludedTree` is not a bridge to `RemainingTerminalRadius`; it pays no id.
- Scan forbidden tokens without relying on `\b` under POSIX `rg`.

## Condensed history

- The frozen B13 census is terminal - sharp - 1997 paid = 389 ids. Only seven
  ids have public tree payloads; the other 382 are absent. Row caps exclude
  those seven for any row count, so wider LP work cannot rescue them. No id paid.
- CI `41201323694` is green for `RefineFourteen` (`paid_count = 2011`) and
  `RefineFourteenMain`. `41217409382` is green for `RefineSixteenRepair`,
  `RefineSixteenResidual`, `RefineSixteen`, and `RefineSixteenMain`, leaving a
  373-id conditional residual. Those interfaces are equivalences, not payments.
- Earlier census failures were proof-encoding, not false ids. Large literal
  `decide +kernel` blocks exceeded kernel limits; cardinality is now structural.
- Missing throughout: radius certificates for the 373 residual ids;
  canonical/geometric packet production; 382 non-public payloads; MPacket
  validity; seven-class and energy premises; root integration.
- No historical host-side audit or byte check is kernel credit.

## 2026-10-31/11-02 - parts 202-290 (condensed)

- Conditional census chain 389->334 (`emit_census_*.py`,
  `EnergyTerminalResidualCensusRefine{350,...,334}.lean`): 55 green ids removed as a
  conditional B13 map, no payment; static verifiers PASS, **CI pending**. Low-id
  repair `EnergyRefineN0039Repair`; archive drafts 3578/3738 + wrappers. Inventory:
  773 files, 7 public payloads, 382 missing, 62/389 source-complete. No id paid.

## 2026-11-03 - parts 291-295 (condensed)

- CI `41449154413`/`41656715257`/`41706645384` `cancelled`; stored run
  `41706645384` (sha `bd5573e5`) exit map: `CensusBase`=0, `C01`-`C04`=1, all
  consumers=1, rest of ~200 lane-C targets 0 -> C01-C04 are the owning reds.
  `chunk0..3` (100/100/100/89) match `residual389-census.json` (static PASS).
  Local bisection INFEASIBLE (`import Mathlib` > 190 s in the probe). No id paid.

## 2026-11-03/04 - parts 296-299 (condensed)

- Part 296 rewrote C01-C04 so each source index gets its own theorem
  `mem_iff_id_<id>` (5011 total) with one `decide +kernel +revert`; each
  `mem_iff_blockNN` delegates via `interval_cases` + `exact mem_iff_id_<id> _ rfl`.
  Interface `mem_iff_block00..50` UNCHANGED. Emitter `emit_census_c01_c04.py`.
- Part 297 added independent static verifier `verify_census_c01_c04.py`.
  Part 298 extended it with the exact-complement check (chunk literals ==
  `residual389-census.json` `residual_ids[0:100]/[100:200]/[200:300]/[300:389]`,
  sorted/dedup, union == 389, `counts.residual == len`). Result:
  `PASS  per-index ids: 5011 (0..5010); blocks: 51; consumer: 51 calls;
  forbidden tokens: none`. Scope: SOURCE-LEVEL STRUCTURE ONLY.
- Part 299 fetched the REAL CI job log for run `41769569707` (sha `da6f0ed3`,
  conclusion failure, 2h51m). Exact owning error (C01, same form C02-C04):
  repeated `(deterministic) timeout at whnf, maximum number of heartbeats
  (200000)` at the `decide +kernel +revert` line of `mem_iff_id_KKKK`, hitting
  exactly the TERMINAL ids. Non-terminal ids pass (`Decidable.and` short-circuits
  at `(data n).terminal = false`). Cause: `Finset.union` value is
  `s - t + t` (`Mathlib/Data/Multiset/UnionInter.lean:45`), so deciding
  `n ∈ paidIDs` (~1997 nested literals) forces ~10^6 diff comparisons. NOT a
  false id, NOT per-index cost per se: the union *value* reduction is the blowup.

## 2026-11-04 - part 300 (exact per-index leaf plan + emitter design)

Re-read GUIDANCE/LANES/C-NOTES/LATEST. No Lean build locally (2 cores; project
not built, `import Mathlib` > 190 s in `/workspace/tools/mathlib-probe`). CI is
the authority. This session did the quantitative extraction needed to emit the
structural (union-free) `mem_iff_id` proof.

New artifact: `n11-work/ops/lanes/C/plan_census_c01_c04.py` (run this session,
rc=0) reads the actual Lean literals and writes
`census-c01-c04-plan.json`. Measured numbers:
- `Paid16GeneralNext505`: 25 literal parts, 505 ids, range `[1160, 2564]`.
- `Paid16GeneralNext1182`: 1182 ids over `[2565, 5007]`, 57 literal sub-blocks
  (8 parts S01..S08; S08 has 1 sub-block of 6 ids). `Next505` is entirely below
  `Next1182` (disjoint ranges, confirmed).
- Terminals (`(data n).terminal = true`, 2506 total) by value range:
  `<1160`: 293; `1160..2564`: 516; `2565..5010`: 1697.
- Consequence: the only indices needing the expensive high-range
  decomposition are the 1697 terminals in `[2565, 5010]`; the 293 low ones need
  no Next1182 reasoning (below its `lower_bound` 2565) and the 516 mid ones need
  no Next1182 reasoning either (same bound); Next505 is below 2565 so the 1697
  high ones need no Next505 reasoning (its `next505_lt` gives `< 2565`).

Emitter design (union-free, decided only on literals <=~210 elements):
1. Non-terminal id: `(data KKKK).terminal = false` by `decide +kernel`, then
   `simp` the iff to `False` and close the census side with `Finset.mem_union`
   decomposition into the four `chunk` literals (each a <=100 linear scan).
2. Terminal id: `rw [EnergyTerminalBatchB13.mem_residualIDs_iff]`, `constructor`.
   Forward needs `(data KKKK).terminal = true`, `KKKK ∉ sharpIDs` (both
   `decide +kernel`) and `KKKK ∉ paidIDs` structural:
   `paidIDs -> B12 | Next1182`, `B12 -> B11 | Next505`, `B11 -> B10 | Rem210`,
   each via `Finset.mem_union`/`not_or`/`push_neg`; leaves: `B10.paidIDs`,
   `Paid16GeneralRemaining210.newIDs` (small nested literal unions, green for
   id 39 in `EnergyTerminalBatchB13Refine0039.lean`), `Next505.newIDs` (one
   `rw [Paid16GeneralNext505.new_mem]; decide +kernel`, <=525 literal compares),
   `Next1182.newIDs` (8 per-part `rw [S0X.new_mem]; decide +kernel`, <=8*168).
   Reverse needs `KKKK ∈ residualIDs` (census), decided per chunk via
   `Finset.mem_union` (<=100 scan each), never the whole union.
3. `mem_iff_blockNN` and the consumer `EnergyTerminalResidualCensus.lean`
   interface stay byte-identical; `chunk0..3` stay byte-identical.

Checks run this session (scope): `plan_census_c01_c04.py` (rc=0, wrote
`census-c01-c04-plan.json`); `git log`/`git status`. NO Lean built locally, no
CI cycle triggered, nothing kernel-checked. Nothing here is kernel credit.

Still unproved (unchanged): CI green for C01-C04 + the red consumers
(`Census`, `Refine0039*`, `Refine0037Refine3149`, `RefineSixteen*Census*`); the
7 red Refine0039/RefineSixteen/Refine385 modules; all 389 residual radius
certificates; 327 source-missing ids; canonical/geometric packet production;
MPacket validity; SevenClassExclusions; arbitrary-centre root theorem.

Very next concrete step: edit `emit_census_c01_c04.py` to emit design (1)/(2)
above (union-free, literal-only `decide`), regenerate C01-C04, re-run
`verify_census_c01_c04.py` (must still PASS; chunk literals unchanged), then
request one CI cycle. Read the FIRST owning error; do not claim green until the
job log shows exit 0 for C01-C04 with axioms
`[propext, Classical.choice, Quot.sound]`.
