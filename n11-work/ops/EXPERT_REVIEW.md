# EXPERT REVIEW — n=11 Lean lanes

**Date:** 2026-10-30 07:19 UTC
**Scope:** HEAD `0361ae51`; required state check, lane operations records, latest CI
artifact, `git log --stat -8`, and the newest Lean/emitter files touched by A/B/C.
Run `41017279843` is in progress on HEAD. The last completed run `41011262474`
is on `9f499ca6`, so its A/B/C diagnostics are stale for the just-merged bytes.
No local full build was run and no Lean/lake/toolchain file was edited.

## Overall

- **No accepted or WIP count moved this round.** C450 is integrated 36/36;
  WIP energy remains 815/2386 with 389 residual IDs, and
  `SevenClassExclusions` remains 0/7. The older accepted handoff in
  `PROJECT_STATE.json` still records only 310/2386, so 815 is a WIP CI credit,
  not a new global acceptance.
- B13 is the one genuine count-moving construction: its own statements prove
  `paidIDs.card = 1997`, but it pays nothing until `B13DescentBounds`, `B13`,
  and `B13Main` all exit 0 on the same committed bytes.
- The just-merged repairs have not yet received matching CI verdicts. The stale
  run confirms green `C450ChainCompletionMain`, `Cos`, `Mono`,
  `Paid16GeneralNext1182`, and `B13Next505Bounds`; it does not judge the new
  Bins, descent imports, explicit row-cap leaves, or peak module.
- Exact `Fraction` audits, static import closure, generator reproduction, and
  hash pins are useful diagnostics only. None raises a mathematical count.

## Lane A

- **C450 is closed; stop spending proof time there.** `C450ChainCompletionMain`
  is CI-green and root-reachable through B12. This still does not make the
  arbitrary-center full-disk theorem unconditional.
- The `hbhi` repair in `SevenClassQ0Deg3Bins.lean` correctly uses the outer
  `h7 : (binIndex k).val ≠ 7`; the impossible `2048 ≤ 1791` branch is gone.
  Bins is nevertheless still deterministically red at line 95: the old CI goal
  `⊢ 0 < ?m.223` comes from `Nat.mod_lt k.val (by norm_num)`, whose modulus is
  not inferred. Use an explicit, typed modulus, e.g.
  `Nat.le_of_lt (Nat.mod_lt k.val (n := 256) (by norm_num))`.
- `EndpointChecks` has no independent verdict while its Bins dependency is red.
  Its restricted 0–4 bridge plus separate 5/6/7 branches remains mathematically
  necessary and should not be weakened.
- `SevenClassQ0Deg3UpperReductionUnimodal.lean` is a genuine reduction:
  `edgeValid_of_monotone` replaces 21×2049 edge checks by 21 exact peak checks
  plus 42 monotonicity facts. The peaks are actual Lean comparisons, not float
  LP or manifest-derived credit. The remaining `EdgeMonotone` premise is real;
  no q0 class is paid yet.
- The peak leaves avoid one oversized kernel check, but each still asks
  `norm_num` to reduce huge `edgeMaxAt` rationals and a degree-29 trig bracket.
  Keep the 21-way split; if a leaf is expensive, split its left value, right
  value, and final comparison, rather than raise heartbeats.
- **Highest leverage after Bins/Endpoint are green:** prove the missing
  full-angle monotonicity ingredient for edge derivatives. The existing
  `cosHiNLag_grid_antitone` is at the half-angle `nodeQ / 2`, so it does not
  directly discharge `edgeHiReal` derivative signs, especially witnesses 9/10
  at `1489 > 1024`. Target
  `cosHiNLag_nodeQ_antitone {k l : Fin 2049} (hkl : k ≤ l) :
   cosHiNLag (nodeQ piHi 2048 l) ≤ cosHiNLag (nodeQ piHi 2048 k)`
  by the same grid scheme as Cos: prove the needed `sinT14` nonnegativity, handle
  the final grid step by an exact closed comparison, then expose one generic
  `edgeIncTo_of_deriv_sign` and one `edgeDecFrom_of_deriv_sign` wrapper. Split
  the 42 leaves into `SevenClassQ0Deg3EdgeShape.lean`; do not use one giant
  `fin_cases`/`norm_num`.
- Even after EdgeValid, `SectorValid`, the strict total, and
  `Q0Degree3AreaInput` remain open. This lane is scoping one of seven classes,
  not closing the global theorem.

## Lane B

- The B13 architecture is sound and mechanically matches the owned data:
  `B12.paidIDs ∪ Next1182.newIDs`, `paid_count = 1997`, and
  `remaining_of_b13` transfers the premise to 389 residual IDs. The separate
  residual-census module also proves the 389 equality; this is real Lean
  accounting, not a manifest count.
- The current descent file now imports both modules needed by `b11_bound` and
  `high_not_next`. The completed red run is therefore a stale-byte result.
  Require the new run to report, in order, exit 0 for
  `EnergyTerminalBatchB13DescentBounds`, `EnergyTerminalBatchB13`, and
  `EnergyTerminalBatchB13Main`.
- Only after those three exact exits 0 should the supervisor replace
  `EnergyTerminalBatchB12Main` by `EnergyTerminalBatchB13Main` in the root and
  credit WIP energy 815→1997. Until then the residual stays 389 and no energy
  credit is paid.
- **Highest leverage:** read the in-progress run at the first B13 error. If
  `high_not_next` is expensive, split its 27×8 expansion into eight part lemmas:
  `high_not_next_part (i : Fin 8) (n : Fin 5011)
   (hn : n ∈ EnergyTerminalBatchB13DescentBounds.b09HighIDs) :
   n ∉ Paid16GeneralNext1182.part i`, then discharge `high_not_next` through
  `newIDs = univ.biUnion part` and `Finset.mem_biUnion`. Keep each leaf near the
  1182 literal inventory; never restore one-shot `decide +kernel` over unions.
- A workflow-level green is not a B13 verdict because the workflow currently
  masks step failure; use `summary.json`/per-target exit lines.

## Lane C

- No energy or class credit has moved. The seven public residual IDs are not the
  seven metric classes, and row caps plus strict gains duplicate facts already
  green in `FrozenCapRationalCore`.
- The latest explicit-summand row-cap leaves address the stale symbolic-sum
  failures, but no matching CI verdict exists. Even if RowCaps becomes green,
  it remains infrastructure with no consumer into `RemainingTerminalRadius`.
- `excluded_*_tree` is conditional on packet equalities `hf0`/`hg` that are not
  consequences of `PaidCellCertificateM.Valid`; it neither proves that a named
  packet is valid nor pays a residual. Its `db_eq_tree` proofs also use large
  `decide +kernel` terms and must not be targeted without a consumer.
- The seven negative frozen-cap results are mathematically useful obstructions:
  no packet with those exact frozen `f0Lo`/`g` values can be `Valid`, for any
  row count. They do not prove the residual radius inequality, which is not an
  existential-packet statement.
- **Highest leverage:** stop emitting more row-cap/witness families. Freeze the
  current bytes and require only the targeted RowCaps verdict. If green, mark
  this route blocked on a missing *positive consumer*: either a public HOST
  payload for one of the 382 absent residual IDs, or a supervisor-approved
  retask to a genuine class exclusion. If a payload is obtained, put its single
  `PaidCellCertificateM.Valid p` plus `common_chart_radius` in a new bridge
  module; one such paid ID would reduce 389 to 388. Conditional wrappers and
  additional hash/reproduction reports are not progress.

## Risks

- **Stale-byte verdicts:** `41011262474` predates the merged B and C repairs.
  Do not carry its B13 or RowCaps failures forward as current diagnostics.
- **Hidden Lane A failure:** Bins still fails before Endpoint and before the new
  peak module; fix `Nat.mod_lt` with an explicit modulus first.
- **Half-angle/full-angle confusion:** the green cosine antitone theorem is for
  `nodeQ / 2`; edge derivatives require full `nodeQ` and witnesses beyond
  `π/2`. Reusing the half-angle theorem would be a false proof step.
- **Resource blowups:** A’s huge rational peak checks, B’s 27×8 high-ID decode,
  and C’s `db_eq_tree` are all at risk of `whnf`/kernel/OOM cost. Split leaves;
  never raise heartbeats or use `maxHeartbeats 0`.
- **Conditional-wrapper false positive:** C’s tree exclusions assume packet
  identifications not present in `Valid`; they cannot be counted as residual or
  class payments.
- **Unpaid premises remain exact:** WIP energy 815/2386, B13 target 1997/2386,
  residual 389, and class exclusions 0/7. The arbitrary-center full-disk theorem
  remains conditional.
- **Root OOM is not a mathematical verdict:** continue serial targeted builds;
  do not convert shared-dependency OOMs into proof failures or successes.
