# EXPERT REVIEW — n=11 Lean lanes

**Date:** 2026-10-29 (UTC)
**Reviewed:** `n11-work/ops/{GUIDANCE,LANES,PROGRESS}.md`, `ops/ci/LATEST.md`, all lane `NOTES.md`/`TARGETS.txt`, `git log --stat -8`, and the newest Lean files touched by each lane. No full `lake build` was run and no Lean/lakefile/toolchain file was edited.

## Overall

- No lane has moved a paid count. Energy remains 815/2386, C450 chain is CI-green in isolation but not root-imported, and `SevenClassExclusions` remains 0/7.
- The current CI snapshot (`40901508838`) shows C450 completion modules green, `FrozenCapRationalCore` and `PaidCellCertificateM` green, but `PaidCellCertificateMCap`, `Paid16GeneralNext1182`, `EnergyTerminalBatchB13`, all SevenClass targets, and root `N11Formalization` red.
- Emitter reruns, manifest inventories, hash pins, Python exact-rational audits, and `project_status.py --check` are not proofs. They are being reported correctly as evidence, but they do not reduce open counts.
- The full root remains OOM-prone: `SharedMomentConcreteSwitchBatch` was killed after 1540s. Root integration must be staged through targeted CI builds, not a full monolithic `lake build`.
- Highest-value global order: root-import the green C450 chain; fix B's mechanical `Next1182` bound errors; fix C's `MCap` rewrite; then build B13 and its root consumer; only then return to SevenClass.

## Lane A

- **C450 telescope: sound.** `source36_paid` is discharged, the empty `remainingSegs` obligation is vacuous, and each `sourceN_remaining_of_remaining` prepends the just-paid segment. This correctly reaches `h450`, `SourceObligation`, and `C450Atom`.
- **But it is not paid globally.** `N11Formalization.lean` still has `HARK-MISSING` comments for both C450 imports and only imports `EnergyTerminalBatchB12Main`. Lane A must make the `ROOT-IMPORT REQUEST` explicit and the supervisor must import `C450ChainCompletionMain`.
- **SevenClass target list is too noisy.** `A/TARGETS.txt` currently builds invalid/red modules (`UpperReduction`, `Counterexample`, `Unimodal`, `EdgeReal`, `EdgeSuffixHigh`) before the analytic base is green. This wastes CI and hides the real Cos/Mono failures.
- **Highest-leverage next step:** set `A/TARGETS.txt` to only `N11Formalization.C450ChainCompletionMain`, `N11Formalization.SevenClassQ0Deg3Cos`, and `N11Formalization.SevenClassQ0Deg3Mono`; keep C450 in the list only until the supervisor imports it.
- For `SevenClassQ0Deg3Cos`, replace the `hasDerivAt_cosHiReal` closing block with explicit nonzero denominators:
  `field_simp [show (28:ℝ) ≠ 0 by norm_num, show ((Nat.factorial 27:ℕ):ℝ) ≠ 0 by positivity]` then `ring_nf`.
- For `SevenClassQ0Deg3Mono`, quote the current CI error against the current imported names before patching; do not reuse stale line numbers.
- Do not emit any further edge/sector proof file until `Cos` and `Mono` are both CI-green.

## Lane B

- **Approach is mathematically sound.** `Finset.univ.biUnion` over the eight `S01..S08` parts, `card_biUnion` with pairwise interval-disjointness, and the B13 `paidIDs = B12.paidIDs ∪ Next1182.newIDs` transfer would reduce the explicit energy residual from 1571 to 389 **if built and root-imported**.
- **Current failure is mechanical, not mathematical.** In `part_s01_bounds` through `part_s07_bounds`, each `exact block_*_bounds n h_*` tries to close a wider part bound with a narrower block bound. This causes the CI type mismatches at lines 276–349 and the dependent errors at 525–531.
- **Highest-leverage next step:** in each of the first seven `part_s*_bounds`, replace the eight exact-block branches with:
  `have hb := block_*_bounds n h_*; exact ⟨hb.1, le_trans hb.2 (by norm_num)⟩`.
- Keep `part_s08_bounds` as the one direct exact block.
- In `new_count`, remove the trailing `norm_num` after the `simp [Fin.sum_univ_succ, part, ...]`: CI line 546 reports `No goals to be solved`.
- Build only `N11Formalization.Paid16GeneralNext1182` until it is green, then expose B13's first independent error. Do not add B13Main or claim 1997 until `Next1182` and `EnergyTerminalBatchB13` are both green and the supervisor imports B13Main.
- Pre-split the two full-set `decide +kernel` proofs `b11_lt` and `next505_lt` in B13 into ≤21-literal blocks; they are the next OOM risk after the dependency is green.

## Lane C

- **`PaidCellCertificateM` is green and mathematically sound.** It is the intended `Fin 7 → Fin m` transport and preserves `Paid16CellCertificate.Valid`. It pays no energy count by itself.
- **`PaidCellCertificateMCap` is mathematically sound but red.** The failure is at the definitional rewrite `rw [rho]` (line 40); the later `rw [hrho]` failure (line 71) is a cascade.
- **Highest-leverage next step:** build only `N11Formalization.PaidCellCertificateMCap` after M, and replace `rw [rho]` with `simp only [DBMMinorantDual.rho]` in `weighted_reduced_le`.
- Do not add row caps, bridges, or wrappers to `TARGETS.txt` until `MCap` is green.
- Unify the duplicated frozen constants: `FrozenCapCertificates` defines `F0/G/y/E` separately from `FrozenCapRationalCore`; make `FrozenCapCertificates` import and reuse the core definitions before any wrapper can be trusted.
- The wrappers are still conditional on `hf0`/`hg` and node identity. The next paid step is one complete node-pinned chain, e.g. for 1409:
  `theorem excluded_1409_tree` with `hnode : p.nodeID = 1409`, `hf0`, `hg`, `FrozenCapRowCap1409.row_cap`, and `FrozenCapRowCapTreeBridges.db_eq_tree_1409`.
- C can affect at most the seven public residual IDs while 382 HOST records are absent. Do not claim any energy/class credit until such a wrapper is green and connected to the residual predicate.

## Risks

- **OOM/giant terms:** B13's `b11_lt`/`next505_lt` use full-set `decide +kernel`; the root full build already OOMs on `SharedMomentConcreteSwitchBatch`. Keep every kernel reduction small and hierarchical.
- **Fake progress:** hash pinning, deterministic regeneration, and Python audits are not CI/paid. `built_count: 1` in a run with many red targets must never be read as progress.
- **Cross-lane dependency:** `EnergyTerminalBatchB13Main` imports `C450ChainCompletionMain`; lane B's final target cannot be credited before A's root integration choice is made.
- **C450 isolation:** green split modules are not the same as the root's frozen goal; root import is the only way C450 becomes a paid increment.
- **SevenClass invalid artifacts:** keep the known counterexample and stale reduction files out of active CI targets so they cannot masquerade as obligations.
- **Lane C data boundary:** no public HOST data exists for 382/389 residual IDs; any plan that claims closure beyond the seven available records is unfounded.
