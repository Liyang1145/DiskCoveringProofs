# Expert review — n=11 Lean lanes

**Date:** 2026-10-31 (UTC)

**Scope:** `n11/work` Lean-bearing HEAD `24e434b4` (ops-only HEAD
`49f04dd8`); CI artifact `13024663395` from run `41150468008`, plus the full
job log behind `ops/ci/LATEST.md`. I read the lane notes/targets, guidance,
status, recent Lean diffs, and current source. No Lean/lakefile/toolchain edit,
no full build, no commit.

## Overall

- **Real progress:** the reconstructed C450 telescope (`C450ChainCompletion`
  and `Main`/`Audit`) is kernel-green, including the source-36 nonempty-tail
  audit. The root still comments out both imports, so this is not yet
  root-reachable credit.
- **Energy:** core B13 is green at `1997/2386` (389 residual). The green
  `RefineThirteen` chain raises the largest currently kernel-paid aggregate to
  `2010/2386` (376 residual in its predicate). The claimed `2013/373` is **not**
  paid: `RefineFourteen` and `RefineSixteen` are red.
- **Seven classes:** still `0/7`. No `Q0RunExclusion`, `Q1RunExclusion`, or
  `SevenClassExclusions` is proved. Lane A has a coherent q0-degree-three
  reduction, but no `Q0Degree3AreaInput` or `Degree3AreaCertificate` instance.
- **CI verdict:** the workflow says `success`, but artifact `summary.json` has
  120 target exits and 47 nonzero. The workflow's trailing `true` is a false
  green. Use the artifact/`=== EXIT ... 0` lines, never the run conclusion.
- **No source `sorry`/`admit`/new axiom/`native_decide`/`ofReduceBool`/
  `implemented_by`/`maxHeartbeats 0` found in the reviewed newest modules.**
  Failed Lean modules can nevertheless print `sorryAx` by error recovery; that
  is an invalid red module, not a hidden proof.
- **Fake/pending progress to reject:** B's `2013/373` static audit and hashes;
  C's 700 exact cap inequalities and hash-pinned tree matches; A's decimal
  slack audit; any workflow-level green check. These are diagnostics or
  generators, not kernel payments.

## Lane A

- **Verdict: mathematically sound direction, operationally misdiagnosed.**
  The all-row bin shapes, sector assembler, and edge/sector table interface are
  a sensible reduction towards q0-degree-three. C450 itself is no longer an
  open proof-construction problem; root integration is the remaining act.
- **Fresh blocker:** `EndpointChecks.lean:257--259` and `:277--279` still fail
  `omega` on the impossible literal branches `j = 5,6,7`. The session-76 note
  that current HEAD repaired this is false: the latest CI log shows the six
  errors and every downstream A target dependency-red.
- **Concrete first fix:** after `fin_cases j`, replace each of the six `omega`
  lines with `norm_num at hj` (or `exact absurd hj (by norm_num)`). Target only
  `SevenClassQ0Deg3EndpointChecks` first; do not bulk-edit downstream modules
  from dependency errors.
- **Then:** require exit 0 for `EndpointChecks`, `UpperReductionUnimodal`, the
  two edge suffixes, `EdgeShape`, all bin modules, `SectorAssembler`, and
  `TableBounds`, in that order.
- **Mathematical gap after green:** `TableBounds` is only the fixed table
  interface. It does not identify `edges R` with a canonical rotated table and
  does not construct `Degree3AreaCertificate`. A useful next signature is
  `theorem areaCertificate_of_table ... (hedges : edges R = image ... ) :
  Nonempty (Degree3AreaCertificate h hr R)`, carrying the strict total proof.
- **No credit:** `sectorValid` does not imply an exclusion until that
  certificate instance exists. The `18,441`-value decimal audit is not proof of
  `totalUpper < piLo`.

## Lane B

- **Verdict: the hierarchical singleton/union approach is sound and is the
  cleanest real count reducer.** `decide +kernel` is limited to tiny singleton,
  disjointness, and literal blocks here; no observed blowup. `Remaining` is
  transferred correctly and the seven-class premise stays explicit.
- **What is paid:** B13 `1997`, then the green Seven/Eight/Eleven/Twelve/
  Thirteen chain at `2010` with 376 residual in the refined predicate. The
  intended sixteen refinements are correct arithmetic (`2013`, `373`), but the
  last three are not kernel-paid.
- **Exact diagnostic:** `EnergyTerminalBatchB13RefineFourteen.lean:62` rewrites
  with `new_count`, whose left side is `newIDs.card`; after the preceding
  rewrites the goal contains `#EnergyRefineN3116.newIDs`, so the rewrite misses.
  `Sixteen` and both Mains then fail only through that dependency.
- **Highest leverage:** repair only `paid_count` with
  `simpa [newIDs] using EnergyTerminalBatchB13Refine3116.new_count` after the
  paid-union/card-union rewrite. Do not touch `paidIDs`, `paid_radius`, or
  `remaining_of`, whose axiom reports are already clean.
- **Acceptance:** fresh serial exit 0 for `Fourteen`, `FourteenMain`, `Sixteen`,
  and `SixteenMain`. Only then record `2013/2386`, residual `373`, and request
  the supervisor-only root switch from `B13Main` to `SixteenMain`.
- **Scope:** this pays sixteen singleton refinements, not the 373 residual
  radii, not `f0Lo`/`g` bridges, and not any of the seven class exclusions.

## Lane C

- **Verdict: exact arithmetic is plausible, but the current proof engineering
  pays nothing and moves neither the energy nor class count.** The seven frozen
  caps are conditional `PaidCellCertificateM` exclusions, not an actual
  terminal-to-packet/radius bridge.
- **Fresh blocker:** all seven `FrozenCapRowCap*` targets are red. In `1409`,
  the two-pass `norm_num [rowA] <;> norm_num [y_1409, db]` still leaves raw
  vector lookups such as `![0,1/8,...] 2`; many strict leaves are unsolved.
  Hash stability and the exact `700/700` audit do not change that.
- **Highest leverage:** stop regenerating 700 monoliths. Refactor **1409 only**
  to prefix form. Define cumulative weights `cum_1409 : Fin 10 → ℚ` and prove
  `weighted_rowA_eq_prefix` for arbitrary `y`:
  `∑ q, y q * rowA i j q = (∑ q, if q.val < j.val then y q else 0) -
  (∑ q, if q.val < i.val then y q else 0)`.
- **Concrete split:** prove ten values with
  `prefix_1409 (t : Fin 10) : (∑ q, if q.val < t.val then y_1409 q else 0) =
  cum_1409 t` by `fin_cases t <;> norm_num [y_1409, cum_1409,
  Fin.sum_univ_succ]`; then `row_cap` by the prefix rewrite plus
  `fin_cases i <;> fin_cases j <;> norm_num [cum_1409, db]`. This replaces 100
  giant closed sums with 10 prefix facts and 100 tiny rational comparisons.
- **Acceptance:** get `FrozenCapRowCap1409` exit 0 before cloning the pattern;
  do not add heartbeats or native evaluation.
- **Mathematical gate:** even seven green row caps do not move `x/2386` or
  `0/7` until an actual packet is constructed, `Valid` is proved, and the
  residual/exclusion consumer is connected. The `hf0`/`hg` obligations and the
  absent 382 payloads remain explicit; the seven exact tree facts are not a
  bridge by themselves.

## Risks

- The overall workflow conclusion is unusable; the artifact currently records
  47 nonzero exits while the job is marked success.
- `EndpointChecks` error recovery produces a `sorryAx` axiom report. Do not
  mistake that artifact for a source `sorry`, but do not call the module green.
- Giant rational tables and repeated closed `norm_num` calls cause long builds
  and unsolved vector-index goals. Prefix/scalar decomposition is the safe
  pattern; raising limits hides the problem.
- B's `373` and C's exclusions are conditional predicates. Neither proves the
  residual radius inequalities themselves, and C has no general packet bridge.
- A's decimal slack and C's exact rational checks establish arithmetic inputs
  only. Kernel inequalities and actual-cover identification remain due.
- Root `SharedMomentConcreteSwitchBatch` still OOMs (exit 137), and the root
  imports neither C450 completion nor B13/Sixteen. A root build is still red
  even after lane repairs until those integration/OOM issues are handled.
- Preserve frozen bytes and exact roots/quantifiers. Manifests, hashes, cached
  verdicts, and float LP search data are not proof credit.
