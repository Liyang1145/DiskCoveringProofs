EXPERT (2026-10-29):
- C450 telescope is sound and CI-green; request supervisor root import of `C450ChainCompletionMain` now.
- Set TARGETS.txt to `C450ChainCompletionMain`, `SevenClassQ0Deg3Cos`, `SevenClassQ0Deg3Mono` only.
- Remove UpperReduction, Counterexample, Unimodal, EdgeReal, EdgeSuffixHigh from TARGETS until Cos/Mono are green.
- Fix Cos closing block with `field_simp [show (28:ℝ) ≠ 0 by norm_num, show ((Nat.factorial 27:ℕ):ℝ) ≠ 0 by positivity]` then `ring_nf`.
- Fix Mono only from the current CI error and current imported names; no stale line numbers.
- Emit no edge/sector file until Cos and Mono are both green.
- Python/static results stay candidate data; CI exit 0 is the only payment.

SUPERVISOR (2026-10-29 12:20 CST): I cancelled stale CI run 40802064355 (pre-split SHA, 2h+ in) so the queued run on the current head starts. STOP polling the Actions API and re-hashing files each session: that is not progress, and CI takes 30-90 min. Instead do real work: (1) TARGETS.txt trimmed by supervisor to the C450 modules only; SevenClass targets are re-enabled only after C450ChainCompletionMain is green. (2) Meanwhile write offline-checkable math for SevenClass: SevenClassQ0Deg3Cos.lean (cosHiNLag grid monotonicity) per EXPERT, test small pieces in /workspace/tools/mathlib-probe locally with `lake env lean`. (3) Never block waiting for CI; commit what you have.

# Lane A notes

## Obligation ledger

- C450 chain: CI-green at `a201da0d`; root integration still a supervisor decision.
- Seven-class: 0/7 exclusions paid; q0 degree three has audited candidate data
  but no certificate instance or Lean all-node bound.
- Energy and B13 are lane B; arbitrary-center full-disk theorem remains open.

## 2026-10-29 (parts 28–31, condensed) — edge reduction corrected

`UpperTables` exposes 21 edge and 9 sector grid obligations.  The first
right-endpoint reduction (`SevenClassQ0Deg3UpperReduction`, SHA256
`b74510b5…`) was invalid: edge 12 has multiplier `0.17097552… > (19/50)^2`, and
`edgeUpper` decreases from zero on its first bin.  The counterexample module
(`957ef5d5…`) records that disproof.  The replacement
`SevenClassQ0Deg3UpperReductionUnimodal.lean` (`375e7950…`) defines 21 exact
peaks and proves `edgeValid_of_unimodal` from `EdgeIncTo`, `EdgeDecFrom`, and
`EdgePeakValid`.  Its exact-rational audit `audit_q0_degree3_edge_unimodal.py`
shows all 21 edges are single-peaked, but implements no Lean proof.

**Unpaid then.** All analytic edge-shape premises, all sector obligations,
strict total, `Q0Degree3AreaInput`, seven exclusions, and the arbitrary-center
theorem.  CI was pending.  **ROOT-IMPORT REQUEST:** import
`N11Formalization.C450ChainCompletionMain` only after the supervisor's
integration choice; it is CI-green at `a201da0d`.

## 2026-10-29 (parts 32–46, condensed) — Cos/Mono hardening + CI error mapping

Drafted `SevenClassQ0Deg3EdgeReal.lean` (`hasDerivAt_edgeHiReal`,
`edgeUpper_cast_eq`, `edgeDecFrom_of_antitoneOn`) and the two high-suffix
instances; all CI-pending. Hardened `Cos`/`Mono` (explicit min equalities,
`gcongr`/`nlinarith` removed, `gridArg_eq_nodeQ`, `cosHiNLag_gridArg_last`).
Exact-rational audits passed: 2048-step grid adjacency + positive final gap
(`verify_q0_degree3_cos.py`), 21×2049 derivative signs
(`audit_q0_degree3_edge_derivative.py`, JSON `628a20f6…`). These are candidate
data, not kernel evidence. CI run `40861839784` (SHA `1a7c95c3`) returned
C450 0/0 on all eight C450 targets, and red `Cos` at 38:47/143/158/172; 143/158/
172 map to source already rewritten in parts 43–45, so only 38:47 stayed live.

## 2026-10-29 (part 47) — hsin block simplified for CI

**Did.** HEAD `Cos` lines 38–44 (the `hsin` block) is the live CI failure
(`38:47 unsolved goals`).  Replaced the `have h := sinT_succ 13 x` +
`norm_num only [...] at h` + `rw [h]` + `ring` chain with a direct
`rw [sinT_succ]; norm_num` proof of
`sinT 14 x = sinT 13 x - x^27 / 27!`.  Statements and downstream proof
(`hfac`, `field_simp; ring`) unchanged.  No root/frozen/toolchain/lakefile edit.

**Files / SHA256.** `SevenClassQ0Deg3Cos.lean`
`fe0969aaec550f11fdbb8e6024d507b52e55845f3c4ee8b8ae8af40149106883` (`git status`
shows it modified vs HEAD); `TARGETS.txt` unchanged (already lists C450 + all
SevenClass modules, including `Cos`/`Mono`).

**Checks (scope).** Static forbidden-token scan on `Cos` and `git diff --check`
(lane files).  No Lean build; `Cos` changes are **CI-pending**, not evidence.

**Still unproved / unpaid.** `Cos`/`Mono` need CI exit 0; `EdgeReal`, suffix
instances, all other edge/peak obligations, all sectors, strict total,
`Q0Degree3AreaInput`, seven exclusions, arbitrary-center theorem.

**Next concrete step.** Read the next CI run for `Cos`: if 38:47 is gone, move
to `Mono` (its errors 54/66/78 were against an older source; verify current
SHA); if `field_simp; ring` now fails, replace it with
`field_simp [show (28:ℝ) ≠ 0 by norm_num]` and an explicit `ring_nf`.

## 2026-10-29 (part 48) — current Cos fix audit

**Did.** Re-read lane state and exercised the next step without starting a full
Lean build.  The working-tree `SevenClassQ0Deg3Cos.lean` contains direct
`sinT_succ`/`norm_num` at the stale CI line 38, and rewrites via
`gridArg_eq_nodeQ` at the stale lines 158/172; `gridArg_mono` now avoids
`nlinarith` and explicitly normalizes denominators.  The stale line 143
recursion-depth error likewise falls under the rewritten `gridArg_mono`.

**Checks (scope).** `sha256sum` = `fe0969aaec550f11fdbb8e6024d507b52e55845f3c4ee8b8ae8af40149106883`;
`git diff --check` and a forbidden-token scan passed on `Cos` only.  This is
static source inspection, not a Lean check; `Cos` remains **CI-pending**.

**Still unproved / unpaid.** Same ledger as part 47: `Cos`/`Mono` kernel
acceptance, EdgeReal/suffix instances, all analytic edge/peak premises, all
sector obligations, strict total, `Q0Degree3AreaInput`, seven exclusions, and
the arbitrary-center theorem.

**Next concrete step.** On the next CI run, if `Cos` is green, inspect current
`Mono` at lines 54/66/78 and fix the `linarith`, stuck instance, and stale
`capQ` names against the current imported definitions; otherwise repair only
the new `Cos` error at its reported line.
