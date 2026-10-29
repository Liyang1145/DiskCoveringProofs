# Lane A notes

## Directives and ledger

- EXPERT: C450 telescope CI-green; keep `TARGETS.txt` at C450ChainCompletionMain,
  Cos, Mono until both SevenClass modules are green.  Do not emit edge/sector work
  before that.  Python/static checks are candidate data; only CI exit 0 pays.
- SUPERVISOR: stop polling Actions/re-hashing; work offline and never block on CI.
- C450 chain: CI-green at `495c970c`; **ROOT-IMPORT REQUEST** for
  `N11Formalization.C450ChainCompletionMain` remains a supervisor decision.
- Seven-class: 0/7 exclusions paid.  q0 degree three has exact-rational candidate
  data, but no kernel green all-node certificate.  Energy/B13 are lane B; the
  arbitrary-center full-disk theorem remains open.

## 2026-10-29 (parts 28–31) — edge reduction corrected

`UpperTables` has 21 edge and 9 sector grid obligations.  The first right-endpoint
reduction (`SevenClassQ0Deg3UpperReduction`, `b74510b5…`) was invalid: edge 12
has multiplier `0.17097552… > (19/50)^2`.  `SevenClassQ0Deg3UpperReductionCounterexample`
(`957ef5d5…`) records the disproof.  `SevenClassQ0Deg3UpperReductionUnimodal`
(`375e7950…`) defines 21 exact peaks and proves `edgeValid_of_unimodal` from
`EdgeIncTo`, `EdgeDecFrom`, `EdgePeakValid`; the exact-rational audit shows all
21 edges single-peaked, but no Lean premise proof exists.

## 2026-10-29 (parts 32–55) — Cos/Mono hardening and diagnostics

Drafted `SevenClassQ0Deg3EdgeReal.lean` and two high-suffix instances
(CI-pending, now off the critical target list).  Hardened Cos/Mono with explicit
natural-min casts, `gridArg_eq_nodeQ`, `cosHiNLag_gridArg_last`, and an explicit
`le_rfl` in the saturated grid branch.  Exact-rational audits passed for 2048 cos
grid steps, the `piHi` cap, 8-bin maxima, 21×2049 edge derivative signs, and the
q0 area/hub graph.  These are not kernel evidence.

Run `40861839784` (`1a7c95c3`) returned C450 0/0 and red Cos; later casts/repairs
were made.  Runs `40893868710` and `40901508838` OOM-killed in unrelated
`SharedMomentConcreteSwitchBatch`, so their SevenClass exit `1` entries are not
Lean diagnostics.  The local cache lacks `IntervalsHighLag.olean` and
`MetricAreaRationalCertificate.olean`; no bounded local project elaboration.

## 2026-10-29 (part 56) — live diagnostics and cast repair

From the run `40901508838` log, confirmed C450 main exit 0 and repaired all live
Cos/Mono diagnostics:
- Cos derivative closing now ends `field_simp; ring` (remaining `+ -x^27`).
- `gridArg_eq_nodeQ` uses `unfold` plus `rw [Nat.min_eq_right hn]`.
- `(min n 2048 : ℚ)` was a rational min; all grid expressions now cast the
  natural min explicitly: `((min n 2048 : ℕ) : ℚ)`.
- Mono:49 replaces mis-oriented `add_le_add_right` with `linarith [hlow]`.

## 2026-10-29 (part 57) — algebra re-audit

Cross-checked derivative closings against `IntervalsHigh.lean`:
`sinT_succ 13`, `factorial_succ 27`, `mul_div_mul_left`,
`hasDerivAt_cosT_succ 13`, `hasDerivAt_sinT 14`, and the `m = 14`
`sin_bound_abs`/`cos_bound_abs` all have the required shapes.  No source edit.
A Mathlib-only probe timed out during import; no local kernel verdict.

## 2026-10-29 (part 58) — current static re-audit

Re-read the current Cos/Mono after part 56 and checked the two derivative sign
lemmas, Taylor remainder bounds, rational casts, `gridArg` minimum branch, and
the saturated final-grid branch against the imported declarations.  No new
source defect found and no source edit made.  Confirmed the latest CI log has no
SevenClass diagnostic: `40901508838` stopped at the unrelated OOM first.

**Files / SHA256.** `SevenClassQ0Deg3Cos.lean`
`aa03f009bfb42be23f4a195812b4a7add4c510733a542bca3d447de79c73b794`;
`SevenClassQ0Deg3Mono.lean`
`463fae364b60604f5e58cca19d57bd0a82d22141d8b0d19cb61fb5dc363b0658`;
`TARGETS.txt` `4bc097e662af98279cd57338e5f29d0e4c5864f770a37777bd318a0deea117cc`.

**Checks (scope).** Static declaration/import comparison; `git diff --check`
passes.  Local project elaboration is unavailable because the imported oleans
are absent.  Cos and Mono remain **CI-pending**, not kernel evidence.

**Still unproved / unpaid.** Kernel acceptance of Cos and Mono; then
`Bins`/`EndpointChecks`; reduction/edge/sector obligations; strict total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-center full-disk theorem.

**Next concrete step.** Read the first live Cos/Mono diagnostic from the next CI
run at the part-56/58 hashes and repair only that diagnostic.  If both exit 0,
re-enable `Bins` then `EndpointChecks` in dependency order.
