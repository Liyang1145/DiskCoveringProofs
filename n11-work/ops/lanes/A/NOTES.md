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

## 2026-10-29 (part 59) — Cos/Mono live diagnostics repaired

Used the full job log for CI run `40914236268` (commit `95df31a3`).  It confirms
the public C450 endpoint, all five completion modules, and
`C450ChainCompletionMain` exit 0.  The remaining lane-A failures were confined
to `SevenClassQ0Deg3Cos` and `SevenClassQ0Deg3Mono`.

Cos repairs: `ring_nf` closes the degree-27 Taylor identity; `gridArg` now uses
the rational min `min (n : ℚ) 2048` so later casts cannot be re-elaborated as
rational mins; `gridArg_eq_nodeQ` uses `min_eq_left`; `gridArg_mono` and both
grid-step branches use matching rational-min inequalities.  Mono: the flawed
`linarith` addition step is replaced by the orientation-safe
`(add_le_add_iff_right _).mpr hlow`.

**Files / SHA256.** `SevenClassQ0Deg3Cos.lean`
`ec95c86ac63a8fb0abc33e87b5240b69c35f875889f0aef011efa85a19cbdc78`;
`SevenClassQ0Deg3Mono.lean`
`e0742534c3bda480b5d5ac4d06d4bba7681995208bc62091aeb0ab26e08ad59e`.
`TARGETS.txt` is unchanged at
`4bc097e662af98279cd57338e5f29d0e4c5864f770a37777bd318a0deea117cc`.

**Checks (scope).** `python tools/project_status.py --check` passes (handoff
index/manifest scope only); `git diff --check` passes; a targeted scan finds no
`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, or
`ofReduceBool` in either module.  A Mathlib-only probe timed out after 120 s
before producing a verdict.  Local project elaboration remains unavailable, so
both modules are **CI-pending**, not kernel evidence.

**Still unproved / unpaid.** Kernel acceptance of Cos and Mono; then the
`Bins`/`EndpointChecks` layer; reduction/edge/sector obligations; strict total;
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-center full-disk theorem.

**Next concrete step.** Supervisor commit should trigger CI.  Read the first
new Cos/Mono diagnostic at the hashes above; repair only that diagnostic.  If
both exit 0, re-enable `SevenClassQ0Deg3Bins` in `TARGETS.txt` first, then
`SevenClassQ0Deg3EndpointChecks` after Bins is green.

## 2026-10-29 (part 60) — candidate-data recheck

Re-read the current uncommitted Cos/Mono repairs and matched every diagnostic
from CI `40914236268` (`95df31a3`) to a changed expression in the part-59
sources.  `python3 n11-work/ops/lanes/A/verify_q0_degree3_cos.py` passed all
2048 adjacent `cosHiNLag` grid steps and the final-step exact-rational
inequality.  This is candidate rational data, not kernel evidence.  A bounded
Mathlib-only probe timed out during import (110 s), so no local Lean verdict was
obtained.  No source edit was needed in this continuation.

**Checks (scope).** `python3 tools/project_status.py --check` passes (handoff
index/manifest declarations only); `git diff --check` passes; the cosine audit
above is exact-rational candidate data over its stated grid.  C450 remains
CI-green; Cos and Mono remain **CI-pending**.

**Still unproved / unpaid.** Kernel acceptance of Cos and Mono; `Bins` and
`EndpointChecks`; reduction/edge/sector obligations; strict total;
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-center full-disk theorem.

**Next concrete step.** Commit the part-59 files and read the first fresh
Cos/Mono diagnostic at hashes `ec95c86a…` / `e0742534…`.  Repair only that line;
if both exit 0, re-enable `SevenClassQ0Deg3Bins`, then `EndpointChecks`.

## 2026-10-29 (part 61) — handoff hash recheck

Re-read the current part-59/60 worktree.  Cos/Mono are still the exact repaired
hashes `ec95c86a…` / `e0742534…`; no new source edit was made in this continuation.
The old CI diagnostics in `LATEST.md` predate these repairs.  `TARGETS.txt` still
contains only `C450ChainCompletionMain`, `SevenClassQ0Deg3Cos`,
`SevenClassQ0Deg3Mono` (SHA `4bc097e6…`).

**Checks (scope).** Local oleans for `IntervalsHighLag` and
`MetricAreaRationalCertificate` are absent, so no local project elaboration was
possible.  Forbidden-token scan of the two modules is clean; C450 remains
CI-green at run `40914236268`.  Cos/Mono remain **CI-pending**.

**Still unproved / unpaid.** Kernel acceptance of Cos/Mono; Bins and
EndpointChecks; reduction/edge/sector obligations; strict total;
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-center full-disk theorem.

**Next concrete step.** From the first CI run committed at the hashes above, read
only the new Cos/Mono diagnostics and repair those lines; if both pass, re-enable
`N11Formalization.SevenClassQ0Deg3Bins`, then `EndpointChecks`.

## 2026-10-29 (part 62) — post-repair state pin

Re-read the part-59/60 worktree and re-hashed the two live targets.  No source
edit was made in this continuation.  `Cos` is still `ec95c86a…`, `Mono` still
`e0742534…`, `TARGETS.txt` still `4bc097e6…`; all three match part 61.
`ops/ci/LATEST.md` is still run `40914236268` at `95df31a3`, whose Cos/Mono
diagnostics predate the part-59 repairs (its summary exit lines are the old
failures), so no fresh diagnostic is available.  The old diagnostic lines map
to rewritten expressions already present in the sources: Cos imports/derivative
block, `gridArg` rational min, `gridArg_eq_nodeQ`, both grid-step branches, and
Mono line 49's `(add_le_add_iff_right _).mpr hlow`.

**Checks (scope).** `sha256sum` over the three files as above;
`python3 tools/project_status.py --check` passes at handoff-index/manifest scope.
No local project elaboration: `IntervalsHighLag.olean` and
`MetricAreaRationalCertificate.olean` are absent.  Cos/Mono remain
**CI-pending**, not kernel evidence.

**Still unproved / unpaid.** Kernel acceptance of Cos/Mono; Bins and
EndpointChecks; reduction/edge/sector obligations; strict total;
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-center full-disk theorem.

**Next concrete step.** Supervisor commit of `ec95c86a…` / `e0742534…`, then
read only the first fresh Cos diagnostic (Cos precedes Mono in `TARGETS.txt`)
and repair that line; once both are exit 0, re-enable `SevenClassQ0Deg3Bins`,
then `EndpointChecks`.

## 2026-10-29 (part 63) — bounded elaboration attempt

Re-read part 61/62.  The live hashes are unchanged: `Cos` `ec95c86a…`, `Mono`
`e0742534…`, `TARGETS.txt` `4bc097e6…`.  A bounded attempt
`timeout 25s lake env lean N11Formalization/SevenClassQ0Deg3Cos.lean` (in
`n11-work/lean`) stopped after 12 s before Lean elaboration: Lake tried to check
out the pinned Mathlib revision and failed because the local package tree has
untracked files that would be overwritten (`EXIT:1`).  Thus this is an
environment/package-checkout failure, **not** a Lean diagnostic and not kernel
evidence.  No source edit was made.  `git diff --check` and the forbidden-token
scan over Cos/Mono are clean.

**Still unproved / unpaid.** Kernel acceptance of Cos/Mono; Bins and
EndpointChecks; reduction/edge/sector obligations; strict total;
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-center full-disk theorem.

**Next concrete step.** Supervisor commit of the two part-59 hashes and obtain a
fresh CI run.  Read only the first fresh Cos diagnostic (Cos precedes Mono in
`TARGETS.txt`) and repair that line; after both exit 0, re-enable
`N11Formalization.SevenClassQ0Deg3Bins`, then `EndpointChecks`.
