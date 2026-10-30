# EXPERT REVIEW — n=11 Lean lanes

**Date:** 2026-10-30 05:44 UTC
**Scope:** HEAD `43b1d43f`; `ops/{GUIDANCE,LANES,PROGRESS}.md`, `ops/ci/LATEST.md`, lane notes/targets, `git log --stat -8`, and the newest Lean files touched by A/B/C. The latest completed run `41001693009` is for `e5875cf8`; run `41008974701` for current HEAD is in progress. No full build was run and no Lean/toolchain/lake file was edited.

## Overall

- **No paid count moved this round.** Energy remains 815/2386 with 389 residual IDs; `SevenClassExclusions` remains 0/7. C450 is 36/36 and transitively imported, but that does not make the arbitrary-center full-disk theorem unconditional.
- The latest completed CI has real positives: `C450ChainCompletionMain`, `SevenClassQ0Deg3Cos`, and `SevenClassQ0Deg3Mono` exit 0. It is red for Bins, EndpointChecks, B13DescentBounds/B13/B13Main, and WideFieldRowCaps.
- The current blockers are concrete source defects, not ambiguous mathematics: Lane A has an impossible Bins branch closed by `norm_num`; Lane B omits imports for APIs it calls; Lane C still performs too much definitional work per row theorem.
- Exact Python checks, source audits, generator reproduction, and hash pinning are useful diagnostics only. They do not replace kernel exits 0, and none of them changes the three open counts.
- Current lane scope is still materially short of the goal: one q0 class table, 1997 of 2386 energy IDs, and zero of seven metric-class exclusions are not a proof of the full disk statement.

## Lane A

- **C450 is finished; stop spending proof time there.** `C450ChainCompletionMain` is CI-green and lies in the root closure through `EnergyTerminalBatchB12Main`; stale `HARK-MISSING` comments are navigation noise.
- The domain split in EndpointChecks is mathematically necessary and is the right repair: the old all-bin bridge is false because bins 5–7 violate `u ≤ 1` and `q ≤ 2`. The current restriction to bins 0–4 plus separate 5/6/7 branches is sound in shape.
- **Bins is still deterministically red.** At `SevenClassQ0Deg3Bins.lean:111`, the outer branch already has `h7 : (binIndex k).val ≠ 7`. The inner `by_cases hbin7` therefore has an impossible equality branch, but that branch rewrites `binHi` to value 2048 and asks `norm_num` to prove `2048 ≤ 1791`. It cannot. Reuse the outer fact directly, e.g. rewrite with `256 * (binIndex k).val + 255` under `if_neg h7` and close by `omega`; do not introduce a second case split.
- EndpointChecks’ present split is plausible but has no matching green CI. Preserve the separate `endpointUpperBin_5/6` remainder branch and the saturated-bin-7 branch; do not weaken the statement or reintroduce universal `u ≤ 1`/`q ≤ 2` lemmas.
- **Highest leverage:** fix only the impossible `hbhi` branch, then require CI exit 0 in order Bins, EndpointChecks (Cos and Mono are already green). If EndpointChecks remains red, isolate the first endpoint declaration and replace broad unfolding by a precomputed rational constant comparison; do not raise heartbeats.
- Even after those two exits, q0 degree 3 is not paid. `EdgeValid`, `SectorValid`, the strict total below `piLo`, construction of `Degree3AreaCertificate`, and finally `Q0Degree3AreaInput` remain open. The next post-green split is per-item `EdgeCheck i k` (21×2049 via `edgeValid_of_unimodal`) and per-item `SectorCheck i k`, followed by one assembled certificate theorem.

## Lane B

- The B13 architecture is the right reduction: `paidIDs := B12.paidIDs ∪ Next1182.newIDs`, `paid_count = 1997`, and `remaining_of_b13` would reduce the energy premise from 1571 to 389 obligations. It is **not paid** until B13DescentBounds, B13, and B13Main each exit 0.
- The descent proof’s structural approach is sound: image membership plus `fin_cases` avoids the old `decide +kernel` traversal of `univ.image`; the corrected 27-ID B09 high classification is mathematically necessary. The twelve `g*_lt` `norm_num` decodes are much smaller than the failed kernel decisions.
- **The current red is a missing-import error, not a failed inequality.** `EnergyTerminalBatchB13DescentBounds.lean` imports neither `EnergyTerminalBatchB11` nor `Paid16GeneralNext1182`, but refers to `B11.paidIDs` at lines 242/244 and `Next1182.newIDs/new_mem` throughout `high_not_next`. Add `import N11Formalization.EnergyTerminalBatchB11` and `import N11Formalization.Paid16GeneralNext1182`; the dependency graph is acyclic.
- After imports, build only DescentBounds first. If `high_not_next` is still expensive, split it into one theorem per high ID, or a new `EnergyTerminalBatchB13HighDisjoint.lean` with `theorem high_not_next_part (i : Fin 8) (n : Fin 5011) ... : n ∉ Next1182.part i`; do not expand all 27×8×57 comparisons in one declaration.
- **Highest leverage:** add those two imports and obtain exit 0 for DescentBounds, then B13, then B13Main. Only then request the supervisor’s root replacement B12Main → B13Main; only then credit 815→1997 and describe residual as reduced to 389.

## Lane C

- `FrozenCapRationalCore`, `PaidCellCertificateM`, and `PaidCellCertificateMCap` are green infrastructure. The exact row caps and strict negative margins are mathematically meaningful, but the wide witnesses duplicate green core witnesses and yield no new exclusion by themselves.
- The seven public residual energy IDs (1409, 2337, 2341, 2356, 2360, 2368, 2370) are not the seven metric-class exclusions. A conditional `excluded_*_tree` assuming absent `hf0`/`hg` is not a paid residual, a paid energy ID, or `1/7` class credit.
- The part-90 row split is not yet a proven cost fix. The completed CI timeouts at the seven old 100-case declarations apply to the preceding bytes; the new declarations still keep ten `j` cases and the same large `yW`/`rowA`/`db` unfolding in each 200k-heartbeat budget. Splitting ten into five is unlikely to address the measured `whnf` cause.
- If the row-cap path is retained, make each theorem one cell with a literal right-hand side, or first prove a generic cumulative-weight formula for `∑ y q * rowA i j q`; then each comparison is a small rational inequality rather than repeated reduction of a 10×10 matrix. This is proof-cost work only, not count progress.
- **Highest leverage:** stop emitting duplicate witness/row-cap families and prove a consumer that can actually pay one obligation, e.g. a positive `PaidCellCertificateM.Valid p` instance for one residual ID together with `common_chart_radius`, or an unconditional theorem that a named residual terminal has no feasible cell. If the available public records only support the present negative/conditional wrappers, mark Lane C blocked on the 382 absent HOST payloads; do not report class or energy credit.

## Risks

- **Deterministic false branch:** Lane A’s `hbhi` tries to prove the false proposition `2048 ≤ 1791`; current Bins cannot become green without repairing it.
- **Missing imports:** Lane B’s dozens of unknown identifiers are upstream imports, not tactic search. Re-running unchanged source will reproduce the same failures.
- **Timeout masking:** both C row caps and A endpoint tables are at risk from `whnf`/`norm_num` expansion. Splitting declarations helps only if each declaration also reduces the unfolded term; raising heartbeats or using `maxHeartbeats 0` is forbidden.
- **Conditional-wrapper false positive:** C’s tree exclusions assume packet-specific equalities not present in `Valid`; never count them as residual or class payments.
- **Unpaid premises remain exact:** energy 815/2386, residual 389, and SevenClassExclusions 0/7 are unchanged. The full-disk bound is still conditional on both energy and class closures.
- **Root OOM is not a mathematical verdict:** `SharedMomentConcreteSwitchBatch` and shared-dependency failures must not be converted into proof failures or successes. Keep CI serial and targeted.
