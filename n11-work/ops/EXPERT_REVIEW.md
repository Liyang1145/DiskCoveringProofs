# EXPERT REVIEW — n=11 Lean lanes

**Date:** 2026-10-29 (UTC)
**Reviewed:** `n11-work/ops/{GUIDANCE,LANES,PROGRESS}.md`, `ci/LATEST.md`, all three lane `NOTES.md`/`TARGETS.txt`, `git log --stat -8`, and the newest Lean files touched by each lane. No full `lake build` was run and no Lean/lakefile/toolchain file was edited.

## Overall

- **No lane has a CI-green mathematical increment.** Energy is still 815/2386 paid, C450 chain integration is drafted/CI-pending, and `SevenClassExclusions` remains 0/7. The notes correctly avoid claiming payment.
- **Structural work is mostly sound, but it is obligation rearrangement, not payment.** Only a green kernel build plus an actual inhabited residual predicate would move a count.
- **Main fake-progress risks are present but not currently misreported:** manifest-derived facts, Python `Fraction` audits, hash pins, and `#print axioms` are evidence only; no lane has claimed them as kernel credit.
- **Three systematic hazards:** giant `decide +kernel`/`norm_num` terms can still OOM the runner; `EnergyTerminalBatchB13Main` imports lane A's `C450ChainCompletionMain`, so serial target order does not isolate B from A; lane C's seven `excluded_*` theorems are conditional and cannot pay any residual energy.
- **Global next action:** first force a green C450 chain, then a green B top transfer, then return to SevenClass. Freeze lane C packet emission until its first target reports.

## Lane A

- **C450 telescope: sound.** `verify_chain_completion.py` passes and the five split files contain all 25 transfers exactly once, from `Source36` (empty tail) to `Source11`; `h450`, `source_obligation`, `c450_atom`, and the consumer signature all match `ActualMetricClassReduction.main_of_seven_class_certificates`.
- **The split is the right OOM fix**, but it is still unverified. Previous failures were in the old monolithic `C450ChainCompletion`, not in the transfer types.
- **SevenClass Q0 degree-three: structurally sound but not paid.** `SevenClassQ0Deg3` is the correct certificate wrapper; `Mono`/`Bins`/`EndpointChecks` give a credible finite-node reduction. `SevenClassQ0Deg3UpperTables` only defines `EdgeValid`/`SectorValid` as premises; no `Q0Degree3AreaInput` or `Degree3AreaCertificate` is inhabited.
- **Highest-leverage next step:** trim `lanes/A/TARGETS.txt` to only `C450ChainCompletionTail`, `Mid1`, `Mid2`, `Mid3`, `C450ChainCompletion`, `C450ChainCompletionMain` until those six are CI green; remove all SevenClass targets from the active list. Do not emit more upper-table files before endpoint/CI success.
- **After C450 green, for SevenClass use analytic sign-crossing, not 2049-case `decide`.** New files:
  - `SevenClassQ0Deg3Cos.lean`: define `cosHiNLag q := cosT 14 q + |q| ^ 28 / (Nat.factorial 28 : ℚ)`; prove grid monotonicity `cosHiNLag (nodeQ U N k) ≤ cosHiNLag (nodeQ U N l)` when `k.val ≥ l.val`, or the equivalent real lemma on `[0, π]`.
  - `SevenClassQ0Deg3EdgeProofs.lean`: for each edge `i`, state `edgeCheck_i : ∀ k, EdgeCheck i k` and prove it from one sign pair: `0 < R2 * cosHiNLag q_left - b_i` and `R2 * cosHiNLag q_right - b_i ≤ 0`, then `sinHiNLag_mono`/`cosHiNLag` monotonicity.
  - `SevenClassQ0Deg3SectorProofs.lean`: for each sector `i` and each of the 8 bins, prove the extremal candidate dominates its bin using the sector derivative sign `R2 * cosHiNLag q / 2 - mu_i`; compare the 8 candidates with `norm_num`.

## Lane B

- **Conditional transfer is mathematically sound.** `Paid16GeneralNext1182` union/disjointness, `EnergyTerminalBatchB13.paidIDs = B12.paidIDs ∪ Next1182.newIDs`, and `remaining_of_b13` would reduce the residual predicate from 1571 to 389 if all four targets build.
- **This is not yet a paid increment.** It creates a weaker explicit `RemainingTerminalRadius`; it does not inhabit it. Do not update the paid count until `EnergyTerminalBatchB13Main` is CI-green and root-imported.
- **The current union is not the prescribed hierarchical `biUnion`.** Rewrite `Paid16GeneralNext1182` as:
  `def part : Fin 8 → Finset (Fin 5011) := ![S01.newIDs, …, S08.newIDs]`
  `def newIDs : Finset (Fin 5011) := Finset.univ.biUnion part`
  then prove `new_count` with `Finset.card_biUnion` plus 28 pairwise `decide +kernel` facts, exactly as HANDOFF §5 says.
- **Remove `set_option maxRecDepth 10000`.** It is a resource-limit increase; hierarchical `card_biUnion` should make it unnecessary.
- **Split B targets into phases.** Build only `Paid16GeneralNext1182` and `EnergyTerminalBatchB13` first. Keep `EnergyTerminalBatchB13Main` out of `TARGETS.txt` until A's `C450ChainCompletionMain` is green, because B13Main imports it and will pull the heavy A dependency anyway.
- **Highest-leverage next step:** split `EnergyTerminalResidualCensus.lean` into four files, one per 100/89-literal chunk plus an assembly file. The current 51 `interval_cases <;> decide +kernel` blocks each decide membership in a semantic `residualIDs` that unfolds to `paidIDs` (1997 elements) and `sharpIDs`; that is the most likely next OOM.

## Lane C

- **Generic row-count machinery is sound.** `PaidCellCertificateM` and `MCap` correctly generalize `Fin 7` to arbitrary `Fin m`, and `of7_valid` preserves the old API. No concrete packet is instantiated.
- **No energy or class count is reduced.** The seven public failure records are not rescued by extra dual rows; 382/389 residual IDs lack public field records, so lane C has no local route to an actual energy payment.
- **The seven `excluded_<id>` theorems are not yet real exclusions.** Each currently lacks `(hnode : p.nodeID = <id>)` and keeps `hcap` as an explicit hypothesis. Without a proved row-cap lemma, they are conditional and cannot be cited as a packet nonexistence result.
- **Highest-leverage next step:** keep only `FrozenCapRationalCore` in `TARGETS.txt` until it is CI-green. Then replace the duplicated heavy rational proofs in `FrozenCapCertificates` with bridges to the core:
  - `f0_1409_core : FrozenCapRationalCore.F0_1409 = F0_1409 := rfl`
  - `g_1409_core : ∀ q, FrozenCapRationalCore.G_1409 q = G_1409 q := by intro q; fin_cases q <;> rfl`
  - `y_1409_core : ∀ q, FrozenCapRationalCore.y_1409 q = y_1409 q`
  - `strict_gain_1409 := by simpa [f0_1409_core, g_1409_core, y_1409_core, endpoint_1409] using FrozenCapRationalCore.strict_gain_1409`
- **Then make exclusions unconditional.** Add `hnode : p.nodeID = <id>` and prove 7×100 row-cap lemmas:
  `theorem row_cap_1409 (i j : Fin 10) : (∑ q : Fin 9, y_1409 q * rowA i j q) ≤ db 1409 i j := by fin_cases i <;> fin_cases j <;> norm_num [y_1409, rowA, db, DBMSourceTree.data]`
  and derive `excluded_1409_of_valid` by supplying `fun a => row_cap_1409 (p.rowFrom a) (p.rowTo a)` after `rw [hnode]`.

## Risks

- **OOM/decide blowups:** `EnergyTerminalBatchB13` compares B11-sized sets against 168-element sets; `EnergyTerminalResidualCensus` does thousands of semantic `decide +kernel`; `FrozenCapCertificates`/`FrozenCapRationalCore` use giant rational `norm_num`. Each needs smaller split modules and fixed lemma lists.
- **`maxRecDepth 10000`** in B files should be removed; keep kernel work below the measured 170–500 literal bound.
- **Cross-lane dependency:** `EnergyTerminalBatchB13Main` imports `C450ChainCompletionMain`, so the current C,B,A build order does not keep A's OOM risk away from B's main target.
- **CI is not currently proof.** `LATEST.md` has no populated summary/build tail; the last completed run was killed during lane A. Counts must remain unchanged until `EXIT 0` is observed for the relevant targets.
- **C450 empty tail caveat:** proving `Source36.remainingSegs = []` pays only the vacuous endpoint; the 25 subsequent segment transfer theorems still have to elaborate before `h450` counts.
- **Python-only evidence** (`probe_*`, `certify_*`, `emit_*`) is useful direction but never a proof; every lane must continue to mark drafts `CI pending` until the exact generated Lean module is kernel-built.
