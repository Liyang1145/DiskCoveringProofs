# Expert review - n=11 Lean lanes
**Date:** 2026-11-02 (UTC)
**Scope:** worktree HEAD `418a765d` (Lean content unchanged since `f6f73fc8`).
Read `GUIDANCE`, `LANES`, `PROGRESS`, `ci/LATEST`, all three lane notes/targets,
recent history, and the newest Lean files. `project_status.py --check` passes
only as a manifest-index check. I did not edit Lean, lakefile, toolchain, or run
a full Lake build.

## Overall

- **Verdict:** there is real prior kernel payment but no fresh current-tree
  verdict. The credible energy total remains `2013/2386` with 373 residual
  terminal radii. `C334` and `B344` are conditional premise rewrites, not paid
  energy. Seven classes remain `0/7`.
- **CI boundary:** `ci/LATEST` records `41449154413` pending on `f6f73fc8`,
  `41449062259` cancelled on `6b9c9f05`, and `41418145317` in progress on the
  older `43c30dbf`. None verifies the current q0(5,8), 3/23, or 334 modules.
  The last useful energy-green artifact is `41352871085` at `b1e15e83`.
- **C450:** the assembled telescope, endpoint audit, and main consumer exist
  and were reported green, but both completion imports remain commented in
  `N11Formalization.lean`. The chain is not root-reachable.
- **Energy root boundary:** the live root still imports
  `EnergyTerminalBatchB12Main` (815 paid), not `RefineSixteenMain` (2013 paid).
  Therefore module credit and root-level credit differ sharply.
- **Evidence discipline:** no reviewed new file contains `sorry`, `admit`, a new
  axiom, `native_decide`, `ofReduceBool`, `implemented_by`, or
  `maxHeartbeats 0`. That is necessary, not sufficient. Multi-kilobyte
  `decide +kernel` terms and `maxRecDepth 100000` remain resource risks.

## Lane A

- **Verdict: C450 is complete pending supervisor root integration; q0(3) is a
  credible 1/7 candidate but unpaid; q0(5,8) is exploratory and not proof data.**
- `C450ChainCompletion.h450` telescopes Source12..36 and the audit correctly
  checks that `source36` is a member, so the empty tail is not mistaken for the
  last segment. No more chain work is needed; only the root import is missing.
- `SevenClassQ0Deg3StrictTotal.q0Degree3AreaInput` and
  `SevenClassQ0Deg3Q0Exclusion.q0_degree3 : Q0RunExclusion 1` form the right
  consumer. They remain CI-pending. A green `q0_degree3` would be exactly one
  class, not a reduction of `SevenClassExclusions`.
- The q0(3) proof still has nine sector-peak leaves and 21 edge-peak leaves
  with terminal kernel checks over roughly 2,000-bit rationals. Large target
  lists make failures hard to localize; repair only the first owner.
- **q0(5,8) concern:** `q0_closure_dual.py` is a SciPy float LP search. The
  committed "exact" source parses nine-decimal output as `Fraction`; rounding
  does not create an exact dual certificate. The strict source evidence is an
  external mpmath interval branch-and-bound run, not a Lean factor-bound
  theorem. The closure algebra in `Q0Degree5ClosureExtension` is sound as an
  interface, but no concrete `ClosureFactorBounds` instance (11 face, 9 switch,
  9 sector) or strict source total exists. No q0(5,8) exclusion is earned.
- **Highest leverage:** put `SevenClassQ0Deg3Q0Exclusion` first in the A target
  list and CI-build only its q0(3) dependency frontier. Required endpoints:
  ```
  theorem q0Degree3AreaInput : SevenClassQ0Deg3.Q0Degree3AreaInput
  theorem q0_degree3 : ActualMetricClassReduction.Q0RunExclusion 1
  ```
  Require both exits `0` and axioms `[propext, Classical.choice, Quot.sound]`.
- **Repair strategy:** split any red `sectorPeakValid_i` or `edgePeakValid_i`
  into its own file and prove `sectorUpper ... ≤ sectorMax i` by explicit
  `sectorUpper`/`edgeUpper` unfolding plus exact rational comparison. Replace a
  failed 2,000-bit `decide +kernel` leaf with denominator-normalized `norm_num`
  lemmas; do not raise heartbeats or introduce decimals. Freeze q0(5,8) until a
  genuinely exact rational closure certificate and Lean bounds exist.

## Lane B

- **Verdict: the B13/sixteen argument is sound and is the only recent paid
  energy reduction. Current residual-bridge work adds no certificate.**
- `EnergyTerminalBatchB13RefineSixteen` and `RefineSixteenMain` are green in
  `41352871085`: `paid_count = 2013`, 373 residual. The incremental/1409/346
  interfaces are logically valid but only restate obligations.
- `EnergyRefineN0003Restored` and `EnergyRefineN0023Restored` are 235 KB and
  213 KB archive drafts with 12 KB lines, `maxRecDepth 100000`, and many
  `constructor <;> decide +kernel` validity proofs. Removing only the banned
  unbounded-heartbeat directive does not establish they compile under the
  default 200,000-heartbeat budget. They currently pay zero.
- The `373 -> 346 -> 344` story is stale relative to C's 334 frontier and
  duplicates lane C. C334 still contains ids `3` and `23`; the coherent
  combined conditional frontier is 332, not a separate 344. Conditional
  frontiers must not be reported as paid counts.
- **Highest leverage:** make id 3 the first genuinely paid post-2013 module.
  Build `EnergyRefineN0003Restored`, its wrapper, then
  `LaneBArchiveRefine3And23.residualCertificate3`. Required endpoints:
  ```
  theorem new_radius ... : SourceExactRoot.sourceRadius < r
  theorem residualCertificate3 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 3
  theorem b13_remaining_of_residual346_omitting_3_23 ... :
    EnergyTerminalBatchB13.RemainingTerminalRadius
  ```
- **Repair strategy:** split `MValid pkN` into one lemma per field
  (`S_pos`, `beta_nonneg`, `beta_sum`, `lines`, `endpoints`, `lam_nonneg`,
  `reduced`, `numeric`) and split packet literals leaf-by-leaf. Use `fin_cases`
  only over `Fin 16/36/9/7`; use exact `norm_num` on each closed field. If that
  still times out, abandon the archive singleton and return to packet production
  for a source-complete residual id instead of adding another wrapper.
- Also request the supervisor switch the root energy import from `B12Main` to
  the CI-green `RefineSixteenMain`; without it the 2013 credit is not in the
  root theorem. The lane note's manifest claim is stale: live `FILES.jsonl` has
  14,547 entries and no `n11-work` entries, not 14,562.

## Lane C

- **Verdict: the 389 -> 334 chain is valid conditional set algebra and presently
  pays nothing. It does not reduce energy below the prior 373 open radii.**
- `EnergyTerminalResidualCensusRefine334` correctly subtracts `{3578,3738}` and
  maps 334 certificates to B13. But its imported refinement modules are marked
  `DRAFT ... NOT compiled`, and every removed id depends on one compiling. A
  premise count over an unbuilt module is not a paid id.
- The restored archive files contain 12-13 KB rational literals and 13-36
  giant `decide +kernel` checks each. Deleting `maxHeartbeats 0` while retaining
  `maxRecDepth 100000` is not a proof repair and is a likely timeout/OOM source.
  The `3578` and `3738` files are especially poor first targets.
- The latest C note claims a static PASS for 334, but unlike 344 there is no
  committed `verify_census_334.py` or audit JSON. The emitter checks only a few
  substrings. Do not treat that prose as an independent complement audit.
- **Highest leverage:** make one small archive refinement real, not another
  bridge. Use `EnergyRefineN0038` (108 lines, 13 validity checks), then its B13
  wrapper and
  ```
  theorem residualCertificate38 :
    EnergyTerminalBatchB13.ResidualRadiusCertificate 38
  ```
  Require `EnergyRefineN0038.new_radius` and the wrapper's `paid_radius` to
  exit `0` with clean axioms before touching 3432 or 3578.
- **Repair strategy:** split each `validN : MValid pkN` by `MValid` field and
  packet leaf; discharge `lines` by `fin_cases` over `Fin 36`, `beta` over
  `Fin 16`, `reduced` over `Fin 9`, and `lam` over `Fin 7`; close each rational
  leaf with `norm_num`. Add the missing independent complement verifier.
- **Queue control:** 232 serial C targets cannot reliably reach the tail within
  the 5-hour CI budget. Put only `0038`, its wrapper, and the census stage needed
  for id 38 at the front; park later 334 links until that block is green.

## Risks

- **False count risk:** `2013/2386` is kernel-backed on an older green commit;
  334, 344, and 332 are conditional frontiers. Do not quote the latter as paid.
- **False green risk:** workflow success can hide nonzero per-target exits, and
  `ci/LATEST` currently has no summary or log for the newest run. Cite exact
  target exits and commit, never job status alone.
- **Root risk:** C450 completion imports are comments and the root energy import
  is still B12. A lane-green module is not a root theorem.
- **Resource risk:** q0 peak decisions, archive `MValid` decisions, and
  `maxRecDepth 100000` can time out or OOM. Split terms; do not raise budgets or
  substitute decimals.
- **Source risk:** the q0(5,8) dual is rounded numerical LP output with an
  external interval certificate. It must not be promoted to exact proof data.
- **Evidence risk:** hashes, manifests, set complements, Python `Fraction`
  checks, float LP output, and `decide` counts are diagnostics only. The delivery
  manifest is not a proof and is currently stale for `n11-work`.
