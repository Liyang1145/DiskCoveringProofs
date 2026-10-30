# EXPERT REVIEW - n=11 Lean lanes

**Date:** 2026-10-30 (UTC)

**Scope:** `n11/work` at `79e52a68`/CI head `ede0d1c8`; `START_HERE.md`,
`project_status.py --check`, lane guidance/notes/targets, `git log --stat -8`,
CI run `41065332260` plus its full job log, and the newest Lean bytes in A/B/C.
No Lean, lakefile, manifest, or toolchain edit; no project/root build; no commit.

## Overall

- The maintained accepted handoff is still C450 `11/36`, energy `310/2386`,
  class exclusions `0/7`, and no arbitrary-center full-disk theorem. The WIP
  tree is not that accepted root.
- Current WIP kernel results are materially better than the handoff: C450
  completion is imported and CI-green; `EnergyTerminalBatchB13Main` is
  CI-green with paid set `1997/2386` and residual `389`; class exclusions remain
  `0/7`.
- The root still imports `EnergyTerminalBatchB12Main`, not B13Main, so the
  root-reachable energy premise is `815/2386` (residual `1571`), and the root
  target is red only after an unrelated `SharedMomentConcreteSwitchBatch` OOM.
  Root-reachable, accepted, and module-conditional counts must not be conflated.
- C450 closure is sound. `drop 36 = []` proves only the source-36 tail; the
  telescope then inserts each `sourceN_paid` while walking back through
  `sourceN_remaining_of_remaining`. This is not an empty-tail shortcut.
- Lane C's green singleton refinements are real conditional theorems, but no
  aggregate consumer is green and B13 still has 389 residual IDs. They have not
  moved the formal B13 paid count or the accepted ledger.
- Lane B's seven row-cap candidates are red and, even if green, have no proved
  `f0Lo`/`g` bridge to `RemainingTerminalRadius`. Their exact rational audit is
  not a certificate payment. Lane A remains at `0/7`, with its newest chain red
  on tactic/proof plumbing rather than a discovered numerical counterexample.
- Fake-progress audit: no float LP, `sorry`, `admit`, new axiom, `native_decide`,
  `ofReduceBool`, `implemented_by`, or `maxHeartbeats 0` was found in the reviewed
  newest files. Hash pins, manifest counts, archive trees, and Fraction audits
  were treated as diagnostics only. The green Lean exits, not those artifacts,
  carry conditional credit.

## Lane A

- **Verdict: mathematically sound direction, no count reduction yet.** The
  q0-degree-three reduction to exact edge/sector maxima is legitimate. The
  cosine-degree-28 monotonicity and exact witness-node thresholds are coherent,
  and the 42 finite edge-shape facts are useful conditional work.
- **Current CI:** run `41065332260` is green through `Bins`, but
  `EndpointChecks` exits 1 with at least 18 diagnostics; all four downstream
  file exits 1 are dependency failures, not independent verdicts. `EdgeShape`,
  `edgeValid`, sectors, strict total, `Q0Degree3AreaInput`, and the exclusion
  are not paid.
- **First real blocker:** `sinT 4` is not unfolded at
  `EndpointChecks.lean:76`, so `ring` cannot prove the quartic identity. The
  later `![...] 5/6` goals show vector lookup is also left unreduced, and the
  `hj : ... < 5` false cases need `norm_num at hj`, not bare `omega`.
- **Highest leverage:** split the 369-line endpoint file into
  `EndpointChecksTaylor.lean` (generic Taylor/monotonicity only),
  `EndpointChecksBins.lean` (eight scalar bin lemmas), and the existing assembly
  file. In the Taylor module prove
  `theorem sinT4_eq_quartic (a : ℝ) : sinT 4 a = a - a^3/6 + a^5/120 - a^7/5040`
  with `simp [sinT, Finset.sum_range_succ]` then `ring_nf`.
- In the bin module use eight scalar definitions `endpointU0 : ℚ := ...`, not
  repeated vector lookups; close each rational branch with
  `simp only [endpointU5, sinPoly4]; norm_num` and keep
  `linarith [Real.pi_gt_three]` for real pi comparisons. Do not add more edge
  shape code until `EndpointChecks` and `UpperReductionUnimodal` exit 0.
- **After that:** prove `SectorValid` before claiming q0-degree-three assembly;
  `EdgeShape.edgeValid` alone does not instantiate `Q0Degree3AreaInput`.

## Lane B

- **Verdict: B13 is technically sound; the row-cap lane is a dead end.** B13's
  union/disjointness/`paid_radius` chain is correct and CI-green, and
  `remaining_of_b13` is the right credit transfer. The seven public frozen-cap
  exclusions still lack the fixed `f0Lo`/`g` hypotheses, so the row caps cannot
  become residual radii without new data or a genuine bridge.
- **Current CI:** all seven `LaneBFrozenCapRowCap*` targets exit 1. The first
  error is `No goals to be solved`; later leaves still contain
  `![...] 2`, `![...] 3`, etc. Thus `norm_num [y, rowA]` is not reducing the
  vector lookup. A mechanical fix would be `simp only [y_..., rowA]` followed by
  `norm_num`, but this would not move the ledger.
- **Highest leverage:** stop adding B Lean content. The supervisor-only change
  remains `N11Formalization.lean:1961`: replace the B12Main import by B13Main,
  then require fresh root CI. No new lemma is needed for that switch.
- Do not claim `1997/2386` root-reachable until that root CI is green, do not
  count row caps as the seven exclusions, and do not reintroduce the residual
  census into B13Main merely to manufacture a consumer. The 389 residual is a
  mathematical input, not a manifest inference.

## Lane C

- **Verdict: real but marginal conditional progress.** The recovered N2341,
  N3040, N2965, N3440, N3589, N3623, N3633, N3777, and N3792 singleton wrappers
  are CI-green with `new_radius` axiom-clean. They are genuine one-ID
  refinements, not hash-pinned claims. N2337's certificate is green but its
  wrapper is red.
- **Aggregation is the blocker.** `RefineSeven`, `RefineSevenMain`, `RefineEight`,
  and `RefineEightMain` are all red. Seven fails on `rcases ... with rfl` and a
  no-goals `norm_num`; Eight inherits that failure. The B13 paid set therefore
  remains 1997 and the residual remains 389.
- **Highest leverage:** repair the aggregate once rather than mining more
  singleton archives. Define
  `def parts : Fin 9 → Finset (Fin 5011) := ![N2341.newIDs, ..., N3792.newIDs]`
  and `def newIDs := Finset.univ.biUnion parts`; prove a single membership iff
  `n ∈ newIDs ↔ n = 2341 ∨ ... ∨ n = 3792`, then use `rw [h]` (not `subst`) in
  each terminal/radius branch. Prove `new_count = 9` through
  `Finset.card_biUnion` with 36 concrete pairwise-disjoint `decide +kernel`
  facts, then expose `remaining_of` and one CI-green Nine/aggregate main.
- Fix `EnergyTerminalBatchB13Refine2337.lean:240` separately with
  `have hval : (2337 : Fin 5011).val = 2337 := rfl; omega` or
  `norm_num at hlt`. Add 2337 only after its wrapper and main are green.
- Do not describe a singleton `paid_count = 1998` as the new B13 count. A count
  becomes usable only through the aggregate `remaining_of`; the accepted ledger
  changes only after root integration.

## Risks

- **Resource substitution:** the root OOM (`SharedMomentConcreteSwitchBatch`,
  exit 137/OOM guard) is an engineering failure, not a proof of B13 or a
  mathematical disproof. Keep the build serial and do not raise heartbeats.
- **Giant-term risk:** lane A's exact rational upper tables and lane C's large
  packet literals (`maxRecDepth 100000`) are CI-sensitive. Prefer scalar leaf
  modules and hierarchical unions; never hide a timeout by accepting a cached
  verdict.
- **Scope conflation:** accepted `310/2386`, root-WIP `815/2386`, B13 conditional
  `1997/2386`, and the 389 residual are four different scopes. C450 integration,
  energy residual, and the arbitrary-center theorem are also distinct.
- **Missing data:** 382 HOST payloads remain absent, and raw exclusion data does
  not imply a radius. No manifest, hash, or LP report can replace a proof.
- **Shape overclaim:** A's 42 drafted edge facts are not 42 paid facts; sectors,
  strict total, and the six other metric classes remain unpaid. `0/7` stands.
