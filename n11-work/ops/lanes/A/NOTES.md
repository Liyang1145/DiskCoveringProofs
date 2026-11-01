EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.

# Lane A notes

CURRENT (session 154): exact-rational checks cover the row-0 bin-3 literal
endpoints as well as its scalar constants. No lane-A kernel verdict exists.

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

## Condensed history

- Sessions 115--132 replayed 21 edge peaks, 21 discrete peaks, 18,441 sector
  points, 72/72 bin witnesses, 18,369 within-bin steps, 63/63 jumps, and
  strict-total slack `0.012092890370999008`. They repaired the edge 1/8
  endpoint comparisons, frozen-`piHi` maxima, `mu (nextSite i)` pairing, and
  peak proof projections. These were source/arithmetic checks only.
- Session 133 refuted the global `SectorAdjacentUnimodal` premise. Row 0 fails
  at 1022 -> 1023 by `7.421500301204045e-5`; the valid route is bin-wise.
- Sessions 134--137 emitted `SectorStepCounterexample` from that decrease. A
  coarse analytic audit proves the endpoint separation, but giant-literal
  `decide +kernel` and direct `norm_num` probes timed out and are not evidence.
- Session 138 re-audited C450: 25/25 transfers, 26/26 source rows, no empty-tail
  shortcut. C450/Main/Audit remain CI-green; root still has both HARK markers.
- Session 140 replaced 30 giant peak rational projections by definitional
  `rfl`; source/import/unfold gates passed, but not kernel acceptance.
- Sessions 142--144 split 21 edge peaks and 9 sector peaks into one-row
  modules plus thin assemblers to bound elaboration memory. All split targets
  remain CI pending.
- Session 148's global-Lipschitz coefficient was false and was replaced in 149
  by a local `cosHiReal x <= 1/2` bound on bin 3.
- Session 150 added `SevenClassQ0Deg3Q0Exclusion` as the exact consequence of
  `StrictTotal.q0Degree3AreaInput`; it introduces no premise and remains CI
  pending.
- Sessions 151--153 repaired the bin-3 half bound: both `cos_bound_abs` and
  `cosHiReal` contribute tail error, so the finite tail was tightened to
  `4^28/28! <= 1/4`. Exact scalar audit passed; probes timed out during import.
- CI runs `41309394801`, `41301935749`, and earlier runs never reached lane A.
  Lane C/B residual censuses exhausted runner memory (exit 143), so no current
  lane-A source has a kernel verdict.

## 2026-11-01 (session 154) -- bin-3 literal endpoint audit

Extended `audit_q0_degree3_bin3_local_cos.py` to recompute, from the frozen
`piHi` and `mu` intervals with exact `Fraction` arithmetic, the actual degree-14
`cosHiNLag` value at node 768. This now checks the two large literals in
`SevenClassQ0Deg3SectorBin3`, not just their scalar side conditions.

**Result.** All six assertions PASS: `q768 <= piHi/2`,
`q768 <= q1023 <= piHi`, `cosHiNLag(q768) <= 1/2`,
`cosHiNLag(q768) <= 2*mu(nextSite 0)/(19/50)^2`,
`4^28/28! <= 1/4`, and `(19/50)^2/4 - mu(nextSite 0) < 0`. The report records
positive exact margins for both literal endpoint inequalities.

**Files / SHA256.** Audit script
`538803695d008adb19285608dc5cd55f32eec2e863ff3215702d2f26fd550690`;
report `1afb85ee843b3201bb5ec987c6b05458e72f1b05f09754492f69ab5133272418`;
unchanged `SevenClassQ0Deg3SectorBin3.lean`
`1f082d0ad68579543fb45910ed703292d447b015f9a473a895767b3500536673`.

**Checks (scope).** `py_compile` PASS; two audit runs were byte-deterministic;
`git diff --check` PASS. This is exact-rational/source evidence only. It does
not cover Lean elaboration, tactic validity, or kernel acceptance.

**Still unproved / unpaid.** `SectorBin3` and its strict-step theorem,
`SectorStepCounterexample`, split peak modules, downstream bin/shape/calculus,
strict total, `Q0Degree3AreaInput`, `Q0Exclusion`, the other six exclusions,
and the arbitrary-centre theorem remain CI pending/unpaid. `TARGETS.txt` is
unchanged.

**Next concrete step.** Resolve the CI dispatch ordering so lane A runs before
the memory-heavy B/C censuses. Inspect the first lane-A red owner, expected to
be among `SectorBin3`, the split peaks, or their immediate dependency. Do not
split further unless that exact target exceeds runner memory.

## 2026-11-01 (session 155) -- bin-3 proof-obligation audit

Added `audit_q0_degree3_bin3_proof_obligations.py` and its report
`q0-degree3-bin3-proof-obligations-audit.json`. The script uses the frozen
exact row-0 data and checks every arithmetic premise of the general
`sectorValue_zero_strict_dec_of_bin3` proof on nodes 768--1023: the certified
cosine ceiling (`cosHiNLag <= 1/2`), the sine-increment bound
`sinHiNLag l - sinHiNLag k <= (q_l - q_k)/2`, the negative coefficient
`(19/50)^2/4 - mu(nextSite 0) < 0`, the resulting upper bound on every pair,
and the exact table values themselves.

**Result.** All 256 nodes and all 32,640 ordered pairs pass. The largest
certified cosine value is below `1/2`; every pair satisfies the proof bound;
all pairs strictly decrease, with minimum exact drop
`3.216484420446041e-05` and zero adjacent failures. This also confirms the
strict 1022 -> 1023 witness independently of the theorem's analytic argument.

**Files / SHA256.** Audit script
`43e56243475545fee1195c40a619d6d134640f806af97cd36d8cf51f78faf27b`;
report `8c8e86e4c938e859a1d65ec176f416d02b17959a7e33f1a2dcf1eafec7e128c3`;
unchanged `SevenClassQ0Deg3SectorBin3.lean`
`1f082d0ad68579543fb45910ed703292d447b015f9a473a895767b3500536673`.
Confirmed that `TARGETS.txt` already declares `SevenClassQ0Deg3SectorBin3`
explicitly; it is unchanged.

**Checks (scope).** `py_compile` PASS; two audit runs produced the same report
SHA256; the earlier bin-3 local-cosine audit PASSed; the source/import checker
PASSed (116 explicit q0-degree3 references across 75 modules); `git diff
--check` PASS. These are exact-rational/source checks only. They do not cover
Lean elaboration, tactic validity, or kernel acceptance.

**Still unproved / unpaid.** `SectorBin3` still has no kernel verdict. The
counterexample, split peaks, downstream bins/shape/calculus, strict total,
`Q0Degree3AreaInput`, `Q0Exclusion`, the other six exclusions, and the
arbitrary-centre theorem remain unpaid. CI still orders C then B before A, so
no lane-A result is expected from the current workflow unless an earlier lane
finishes within its memory/time envelope.

**Next concrete step.** Obtain an A-first CI build (or a cached isolated
lane-A job) and inspect the first red owner. If `SectorBin3` is red despite
this audit, diagnose elaboration of its big-rational `norm_num` endpoints or
the `exact_mod_cast` bridges; do not alter the arithmetic conclusion.

## 2026-11-01 (session 156) -- old peak failure attributed and isolated

Retrieved the public job log for run `41182882564` (commit `7f7e6f3b`).  Its
first lane-A owner failures were the monolithic `UpperReductionUnimodal` peak
proofs (21 `norm_num` unsolved goals) and `SectorPeak` (unqualified
`nextSite`, then 9 unsolved goals).  The failure was not a false peak: it was
full unfolding of the giant peak table plus a namespace omission.

The current split already fixes the namespace and projects each peak maximum
through an exact `rfl` rewrite before `norm_num`.  Local checks PASS:
`check_q0_degree3_peak_max_projection.py` (21+9 exact `rfl` projections),
`check_q0_degree3_edge_peak_split.py` (21 bodies byte-preserved),
`check_q0_degree3_sector_peak_split.py` (9 bodies byte-preserved), and
`check_q0_degree3_imports.py` (116 references / 75 modules).

I also attempted an isolated Mathlib probe for edge 0 using the exact frozen
coefficient/node/`piHi` and audited maximum.  The probe timed out at 180 s
with no output, and the local probe project Mathlib oleans are incomplete
(`Mathlib.Data.Rat.Defs.olean` is absent), so this attempt gives **no kernel
verdict**.  The current CI run `41318867156` stopped in lane B at
`EnergyTerminalBatchB13RefineSixteenResidualCensus` (OOM kill, exit 137), so
lane A still has no kernel verdict.

**Files / SHA256.** `check_q0_degree3_peak_max_projection.py`
`ca94478e58d2062c2c38473b5f2e54d4b0e5636e0e9bd90cafac84011ff58aed`;
`check_q0_degree3_edge_peak_split.py`
`199f2a135dc53fe957cf6aa58caf477e18ef825d92726dcb239de3f7814ca25f`;
`check_q0_degree3_sector_peak_split.py`
`8116335b536744368ab67825e5cc005d7df0c9691eea0d0eeed8409ac84ff4f0`.

**Still unproved / unpaid.** All split peaks and downstream shape/calculus,
bins, strict total, `Q0Degree3AreaInput`, `Q0Exclusion`, the other six
exclusions, and the arbitrary-centre theorem remain CI pending/unpaid.

**Next concrete step.** Get an A-first isolated CI job.  If it is green through
`UpperReductionUnimodal` and `SectorPeak`, proceed to the first shape/suffix
owner; if not, use the projected-literal probe pattern to diagnose that exact
row without changing the audited arithmetic.
