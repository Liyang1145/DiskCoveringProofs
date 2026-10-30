# EXPERT REVIEW — n=11 Lean lanes

**Date:** 2026-10-30 (UTC)
**Scope:** HEAD `88918335`; `ops/{GUIDANCE,LANES,PROGRESS}.md`, `ops/ci/LATEST.md`, lane notes/targets, `git log --stat -8`, and newest lane Lean. Run `40998371772` is in progress; completed run `40988698121` applies to `2fdf1a1c`, not current bytes. No full build was run and no Lean/toolchain/lake file was edited.

## Overall

- **No paid count moved this round.** Energy is still 815/2386; C450 is 36/36 and transitively root-imported through `EnergyTerminalBatchB12Main`; `SevenClassExclusions` is still 0/7.
- The old C450 `HARK-MISSING` comments are stale navigation text, not an import gap. `EnergyTerminalBatchB12Main` imports `C450ChainCompletionMain`, so C450 is in the root closure. The root remains conditional and red because energy/classes are unpaid and `SharedMomentConcreteSwitchBatch` OOMs.
- `Next1182` alone does not move the energy count. B13 must be green to credit 815→1997; its current descent proof is unpaid and uses a recursion workaround rather than eliminating the bad kernel reduction.
- Lane C’s newest files are sound proof-cost repairs but duplicate already-green core witnesses. Its exclusion wrappers are conditional on `hf0`/`hg`, are not linked to `RemainingTerminalRadius`, and therefore reduce neither 389 residual IDs nor 0/7 class exclusions.
- Reviewed source hashes: EndpointChecks `fddea813…`, B13DescentBounds `075b663a…`, WideFieldWitnesses `f4c758dd…`.

## Lane A

- **C450: sound and closed.** `source36_remaining`/vacuous tail and the `sourceN_remaining_of_remaining` composition produce `h450`, `SourceObligation`, and `C450Atom`; CI independently shows `C450ChainCompletionMain` exit 0. Do no more C450 proof work.
- The current Cos/Bins edits address the old CI lines (`simpa` at Cos 205; explicit div/mod and `Rat.cast_le` in Bins). They are plausible but only current-CI pending. Mono is already green.
- **EndpointChecks has a real domain error, independent of CI.** The low-denominator bridge requires `u ≤ 1` and `q ≤ 2`; however bins 5–7 have `endpointUBin 5/6/7 = 11774/10000, 13737/10000, 15708/10000 > 1`, and `nodeQ_binHi 5/6/7 > 2`. Thus `endpointUBin_le_one` and `nodeQ_binHi_le_two` are false as universally stated, and `endpointCheck_of_quartic` cannot be used for bins 5–7.
- **Highest leverage:** split the endpoint proof by domain. Keep `capQ_le_sinPoly4_of_u_le` only as a `Fin 5 →` lemma for bins 0–4.
- For bins 5–6, use `SevenClassQ0Deg3Mono.capQ_mono` plus `sinHiNLag_mono` with rational upper arguments `11774/10000` and `13737/10000` (both below `RatInterval.piLo/2`), then close each finite comparison by `norm_num [capQ, sinHiNLag, sinTQ, RatInterval.piLo]`.
- For bin 7, use `piHiCapSaturated` to force `capQ (nodeQ … 2048) = 19/50`; prove `19/50 ≤ sinLoNLag (1949/5000)` directly by `norm_num [sinLoNLag, sinTQ]`. Do not use the monotone quartic bridge past 1.
- Delete or restrict the two false universal lemmas; do not “fix” them with `maxRecDepth` or a larger heartbeat budget. Then require CI exits 0 for Cos, Bins, EndpointChecks in that order.
- Even after this, q0 degree 3 is not paid: `EdgeValid`, `SectorValid`, strict total below `piLo`, construction of `Degree3AreaCertificate`, and `Q0Degree3AreaInput` remain open. No exclusion is bought by node tables alone.

## Lane B

- `Paid16GeneralNext1182` and Next505 bounds are CI green. B13’s `paidIDs`/`paid_count`/`paid_radius` design is mathematically the right reducer and would credit 1997/2386, but only after B13 and B13Main build and the root consumer is switched from B12Main.
- The current `maxRecDepth 10000` is a workaround, not progress. The failing decisions `g03_lt`…`g12_lt` quantify over `Paid16GeneralGxx.newIDs := univ.image nodeID`, so `decide +kernel` traverses a 5011-element universe and then hits kernel recursion. The claimed “at most 58 literals” describes the set size, not the computation Lean performs.
- **Highest leverage:** replace each such decision with image membership and finite cases, for example:
  `obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn; fin_cases i <;> norm_num [Paid16GeneralG03.nodeID]`.
  Do the same for `first42_lt` after splitting the union, and for `b09_bound` after splitting B08 from `Paid16Batch22Consumer.newIDs`; then remove `set_option maxRecDepth 10000`.
- The corrected B09 high-id classification is mathematically necessary: the former `b09_lt` was false. Keep it, but do not count the 27×57 `high_not_next` expansion as evidence until it builds. If it remains expensive, add a generic “not in any part” lemma rather than expanding more cases.
- Build only `EnergyTerminalBatchB13DescentBounds`, then B13, then B13Main, requiring exact exit 0 at each stage. No 1997 credit before B13 is green; no root import request before B13Main is green.

## Lane C

- `FrozenCapRationalCore`, `PaidCellCertificateM`, and `PaidCellCertificateMCap` are green and mathematically sound. Their exact rational checks are useful, but M/MCap are infrastructure and pay no energy ID.
- The newest `yW_*` witnesses are exactly `FrozenCapRationalCore.y_*`; the subsequent `simpa using strict_gain_*` is a valid proof-cost repair, not a new exclusion. The “wide” row caps therefore duplicate existing caps rather than adding a new field/edge argument.
- The node wrappers still assume `hf0` and `hg`. No theorem derives those equalities from `Packet.Valid`, and no theorem links `excluded_<id>_tree` to `EnergyTerminalBatchB13.RemainingTerminalRadius` or the 389 census. A green conditional `False` buys no energy or class credit.
- The seven public energy residual IDs (1409, 2337, 2341, 2356, 2360, 2368, 2370) are not the seven metric-class exclusions. They must never be reported as “1/7 classes”.
- **Highest leverage:** stop emitting duplicate witness/row-cap families. Prove one unconditional obligation, e.g. `theorem no_valid_1409 : ¬ ∃ (m : ℕ) (p : PaidCellCertificateM.Packet m), PaidCellCertificateM.Valid p ∧ p.nodeID = 1409`, and either derive `hf0`/`hg` from a fully specified actual packet or refute the current wrapper strategy. If that cannot be connected to the energy residual predicate, report the lane as non-counting and stop.
- Until one such theorem is green and linked, `TARGETS` should contain only modules needed to diagnose that exact theorem; broad wide/four/five regeneration is CI waste.

## Risks

- **False endpoint bridge:** the most immediate technical defect is the all-bin `[0,1]`/`q≤2` quartic transfer; bins 5–7 violate both hypotheses.
- **Kernel blowup:** B13’s `decide +kernel` over `univ.image` is the measured deep-recursion source. Raising `maxRecDepth` masks it and increases OOM risk; it is not a proof strategy.
- **Conditional-wrapper false positive:** C’s `excluded_*_tree` statements look like exclusions but are conditional on source-payload equalities absent from `Valid`; never count them as paid residuals.
- **Stale CI:** `LATEST.md` currently leads with an in-progress run. Only `=== EXIT 0` for the matching source hash is credit; completed `40988698121` diagnostics belong to `2fdf1a1c`.
- **Root monolith:** `SharedMomentConcreteSwitchBatch` still OOMs. Keep serial, targeted CI; do not infer mathematical failure from exit 137.
- **Unpaid global theorem:** C450, energy, and class exclusions are separate scopes. None of the current lane work establishes the arbitrary-center full-disk theorem.
