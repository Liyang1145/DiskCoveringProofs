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

## 2026-10-29 (parts 56–63) — compact diagnostics ledger

CI `40914236268` confirmed C450 and all five completion modules green.  The old
Cos/Mono failures were repaired: degree-27 Taylor closing uses `ring_nf`;
`gridArg` uses the rational min `min (n : ℚ) 2048`; `gridArg_eq_nodeQ` and the
saturated final-grid branch use explicit casts/minimum lemmas; Mono line 49 uses
`add_le_add_iff_right`.  Repeated re-reads found no additional source defect;
local project elaboration remains unavailable because `IntervalsHighLag.olean`
and `MetricAreaRationalCertificate.olean` are absent.  A bounded Lake attempt
failed during package checkout, not Lean elaboration.  Exact-rational audits
passed for 2048 cosine steps, the `piHi` cap, and eight bin maxima; these are
candidate data, not kernel evidence.

## 2026-10-29 (part 64) — latest CI split and Bins hardening

Read the completed CI summary `40935785584` at `cea391a9` (before the part-59
repairs): C450 main exit 0, **Mono exit 0**, Cos exit 1 with diagnostics at
Cos:134 and Cos:196.  The current `Cos` source (`ec95c86a…`) already replaces
both diagnosed proof shapes.  The newer run `40949277719` was in progress at
`f30e46f0`, which includes the repaired lane-A commit; it is **CI-pending**, not
a claim of green.

Audited the next dependency, `Bins`, and repaired one latent issue: the bin-7
nonnegativity proof at line 114 used bare `positivity` on opaque
`RatInterval.piHi`.  It now unfolds `nodeQ` and supplies
`0 ≤ RatInterval.piHi` explicitly, matching the proven `Cos` pattern.

**Files / SHA256.** `SevenClassQ0Deg3Bins.lean`
`e0be98d5b82f714c2872e48b2474ded301a34a9f02ab2e33d6b2a88d816c0465`;
`SevenClassQ0Deg3Cos.lean`
`ec95c86ac63a8fb0abc33e87b5240b69c35f875889f0aef011efa85a19cbdc78`;
`SevenClassQ0Deg3Mono.lean`
`e0742534c3bda480b5d5ac4d06d4bba7681995208bc62091aeb0ab26e08ad59e`;
`TARGETS.txt`
`4bc097e662af98279cd57338e5f29d0e4c5864f770a37777bd318a0deea117cc`.

**Checks (scope).** `verify_piHi_cap.py`: exact positive slack
`sinHiNLag(piHi/2) - 1`.  `audit_q0_degree3_area.py`: exact q0 interval,
11 mu intervals, lambda, upper `< pi`, canonical 21-edge graph, hub degrees
3/10.  `probe_q0_degree3_binmax.py`: exact coverage of all 2049 nodes, cap max
at each of eight right endpoints, positive NodeValid margin.  `git diff --check`
passes; forbidden-token scan of Cos/Mono/Bins is clean.  These checks prove no
Lean theorem; no local project elaboration is possible without the missing
oleans.

**Still unproved / unpaid.** Kernel acceptance of current Cos; then Bins and
EndpointChecks; UpperTables reduction/edge/sector premises; strict total;
`Q0Degree3AreaInput`; all seven exclusions; arbitrary-center full-disk theorem.
`Bins` edit is not yet in any CI run.

**Next concrete step.** Supervisor commit `e0be98d5…` and let CI run the three
current targets.  If current Cos is exit 0, add
`N11Formalization.SevenClassQ0Deg3Bins` to `TARGETS.txt`, then
`N11Formalization.SevenClassQ0Deg3EndpointChecks` after Bins is green.  If Cos
is red, repair only its reported line.

## 2026-10-29 (part 65) — promote Bins/Endpoints; probe cost

Promoted the dependency chain in CI: `TARGETS.txt` now lists C450Main, Cos,
Mono, Bins, and EndpointChecks.  The only pending source repair was already
present as the `Bins` positivity unfolding (`e0be98d5…`); no further source
change was needed.  This does **not** claim Bins or EndpointChecks green.

Re-ran `probe_q0_degree3_binmax.py`: PASS, 8 bins cover all 2049 grid nodes,
every `capQ` maximum is at its bin endpoint, and the exact minimum endpoint
slack is positive.  This is candidate data, not kernel evidence.

Added `probe_endpoint_normnum.lean`, a standalone Mathlib-probe copy of the
endpoint definitions.  A one-endpoint `norm_num` proof (`endpointCheck_0`) did
not finish within 100 s on the two-core sandbox; the combined eight-endpoint
attempt did not finish within 150 s.  Therefore the current EndpointChecks
`norm_num` strategy is likely CI-expensive even if correct.  No project-module
elaboration was attempted.

**Files / SHA256.** `SevenClassQ0Deg3Bins.lean`
`e0be98d5b82f714c2872e48b2474ded301a34a9f02ab2e33d6b2a88d816c0465`;
`TARGETS.txt` `2935e4bd66f363b6f4d3e268539896f60d39213fa3fe37f1606b7c41ad867c3b`;
`probe_endpoint_normnum.lean`
`4b27172f9f1727c00a32c818175689602e5099bcd27892d68c55e65eb09a38b8`;
`q0-degree3-binmax.json`
`f582c26c9e0688526078881f12ce2b3be54231b595a3d6eda54fd8c86a82add0`.

**Still unproved / unpaid.** Kernel acceptance of Cos, Bins, EndpointChecks;
UpperTables edge/sector premises; strict total; `Q0Degree3AreaInput`; all
seven exclusions; arbitrary-center full-disk theorem.

**Next concrete step.** Replace the expensive endpoint polynomial comparisons
with coarse bounds exploiting the large slack: `capQ(q) ≤ 19/50` and a
low-degree lower bound `sinLoNLag a ≥ a - a^3/6` (or `a/2`) on
`a ∈ [0,1]`, then discharge one exact rational bound per table entry.  First
check the existing `IntervalsHighLag` Taylor/remainder lemmas for a reusable
lower polynomial theorem; otherwise add a small lemma in a new endpoint module.

## 2026-10-29 (part 66) — endpoint cost decomposition tested

A 45 s probe of the cheaper endpoint target timed out; raw 14-term unfolding is
not viable.  The planned `sinLoNLag_lower` / `Real.sin_ge_sub_cube` reduction is
superseded by the part-67 `capQ_le_sinPoly4` draft.  No kernel claim.

## 2026-10-29 (part 67) — endpoint polynomial reduction drafted

`SevenClassQ0Deg3EndpointChecks.lean` now uses `sin_bound_abs 4` plus
`sin_bound_abs 14` to bound endpoint caps without expanding the 29-term series
(`capQ_le_sinPoly4`); **drafted, CI pending**.  SHA256 of the Lean file is
`5e522766ce46a64f722f1bfa4f4044dce33219c8da02d5695e861eb7dd036656`.  The
companion verifier passed all 8 exact comparisons (minimum slack about 3.44e-5).
A 140 s Mathlib-probe attempt timed out and project oleans are absent, so there is
no Lean elaboration.  Kernel acceptance of Cos, Bins and EndpointChecks remains
unpaid, followed by UpperTables premises and the global theorem.

## 2026-10-30 (session) — offline audit refresh, no Lean edits

`verify_q0_degree3_endpoint_polynomial.py` PASS (8 comparisons, min slack ≈3.44e-5);
`audit_q0_degree3_area.py` PASS (q0, 11 mu intervals, lambda, upper < pi; canonical
21-edge graph, hub degrees 3/10); `probe_q0_degree3_binmax.py` PASS (8 bins cover
all 2049 nodes, min slack ≈3.43e-5). Forbidden-token and `git diff --check` clean;
no Lean edit or local elaboration (missing project oleans).

**Still unpaid.** Cos (CI pending), Bins, EndpointChecks; UpperTables `EdgeValid`/
`SectorValid` (21×2049 + 9×2049 premises) undrafted; strict total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-center theorem. C450 CI-green.

**Next.** If Cos green, promote UpperTables after Bins/EndpointChecks and begin
`EdgeValid` via `edgeValid_of_unimodal`; if red, repair only its first failure.

## 2026-10-30 (part 2) — audit refresh; unimodal peaks confirmed

Exact-rational Cos, edge-derivative, edge-unimodal and endpoint checks all passed;
no Lean edit or local elaboration.  These are candidate data, not kernel evidence.

## 2026-10-30 (part 3) — Cos minimum-coercion repairs drafted

CI `40935785584` (`cea391a9`) is green for `C450ChainCompletionMain` and red for
`SevenClassQ0Deg3Cos` at 134/196. Replaced fragile `exact_mod_cast`/chained
`apply min_eq_right` with explicit `Rat.cast_le.mpr` witnesses to
`min_eq_left`/`min_eq_right`; this changes coercion normalization, not the statement.

**File / SHA256.** `SevenClassQ0Deg3Cos.lean`
`79cc2b786100ca186e4e457a7386801a0a905e4b2e3dfa2d11aff08b75243715`; Cos is
already in `TARGETS.txt`, so no new module/target.

**Checks (scope).** `git diff --check` and forbidden-token scan clean. Minimal
Mathlib-probe checks timed out (60 s) without elaboration; project oleans are absent,
so this is **drafted, CI pending**, not green or paid.

**Still unpaid.** Cos kernel acceptance; Bins; EndpointChecks; EdgeUnimodal/Sector
premises; strict total; `Q0Degree3AreaInput`; seven exclusions; arbitrary-center theorem.

**Next.** If Cos green, draft `SevenClassQ0Deg3EdgeUnimodalValid` (21
`EdgePeakValid` comparisons plus monotonicity from `cosHiNLag_grid_antitone`); if red,
repair only the first reported proof line.

## 2026-10-30 (parts 4/6) — portable C450 audit; Cos casts explicit

`audit_c450_telescope_local.py` wraps the frozen Windows-path verifier: 25/25
transfers S=12..36, both terminal facts, 26/26 drop/count rows, 0 violations.
All three `min` witnesses in `SevenClassQ0Deg3Cos.lean` now state explicit
`(2048 : ℚ)` and natural-cast types.  Cos is **drafted, CI pending**; no local
project elaboration (missing oleans).  Exact-rational pi-cap/area/binmax audits
pass.  C450 remains historically CI-green; its root-import request is still a
supervisor action.

## 2026-10-30 (part 7) — endpoint cost measured; low-denominator data emitted

Rechecked the endpoint proof direction: the degree-14 absolute-remainder lower
half is valid (`sinLoNLag = sinT14-r29`, `sinT14 >= sin-r29`).  A standalone
Mathlib probe then timed out at 120 s on only two `norm_num` endpoint tables, so
the exact-`piHi` polynomial expansion is not a practical CI strategy.

Added `audit_endpoint_low_denom.py`: exact `Fraction` checks for eight rational
upper bounds `u_j` on `q/2` (denominators ≤10000), using
`sinPoly4(u_j)+1/9!+2/29!` against the existing endpoint lower bound.  All eight
pass; minimum slack is `3.44080645729e-5` (bins 0/1), next 5.92449461989e-5 (bin
7).  On `[0,1]`, `sinPoly4' >= 1-1/2-1/720 > 0`, giving the monotonicity needed
to transfer `q/2 <= u_j` to the polynomial cap.  This is candidate data, not Lean
evidence.

**Files / SHA256.** `SevenClassQ0Deg3Cos.lean`
`a7bb73c442dad852c6e3423a18e001625f5c682cac4573e61ead901f184293c1`;
`audit_c450_telescope_local.py`
`2034e0add2481231b547c73a336c32e04b89eed5cc2a0e02e5ab8067fc34cbee`;
`audit_endpoint_low_denom.py`
`c5e41aa104562b949853cd74175e9361b5255e2a856cdb3f05fde13aae4e2157`;
`TARGETS.txt` `500cc3707072af67a662fb6d14a5636560ccf462ae3a9f990f0e75350e01fbf4`.

**Checks (scope).** `git diff --check`, forbidden-token scan, portable C450 source
audit, endpoint-polynomial audit, binmax audit, and the new exact low-denominator
audit.  No project Lean module was elaborated locally.

**Still unpaid.** Cos kernel acceptance; Bins and EndpointChecks kernel
acceptance; edge/sector premises; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  `TARGETS.txt` now queues the full
dependency order C450Main, Cos, Mono, Bins, EndpointChecks.

**Next.** Add `sinPoly4_mono_Icc01` and `capQ_le_sinPoly4_of_le` to
`SevenClassQ0Deg3EndpointChecks.lean`, replace each endpoint `norm_num` argument
by its explicit `u_j` (from the audit), then run a bounded probe of one endpoint.

## 2026-10-30 (part 8) — polynomial monotonicity added

Added to `SevenClassQ0Deg3EndpointChecks.lean` the real lift `sinPoly4Real`,
cast lemma, derivative formula, derivative nonnegativity on `[0,1]`, and
`sinPoly4_mono_Icc01`: for rationals `0 ≤ a ≤ b ≤ 1`, `sinPoly4 a ≤ sinPoly4 b`.
Proof uses `monotoneOn_of_deriv_nonneg`; derivative is bounded below by
`1 - 1/2 + 0 - 1/720 > 0`. This is the transfer lemma needed to use the
low-denominator `u_j` caps from `audit_endpoint_low_denom.py` instead of a large
exact-`piHi` expansion.

**Files / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`d10589caf935c36fb772394d368b8b4ed8da3f34ee9c8756ddbbd733b512968d`.
EndpointChecks is already in `TARGETS.txt`; no new target.

**Checks (scope).** `git diff --check`, forbidden-token scan. No project
elaboration: this worktree has zero project `.olean` files, and the Mathlib
probe cache contains only a stub `Mathlib.olean`. Status: **drafted, CI pending**,
not paid.

**Still unpaid.** Kernel acceptance of Cos, Bins, EndpointChecks; the eight
low-denominator endpoint inequalities; `EdgeValid`/`SectorValid` premises; strict
total; `Q0Degree3AreaInput`; seven exclusions; arbitrary-center theorem.

**Next.** Add `capQ_le_sinPoly4_of_le` using the audit `U_BIN` values and
`sinPoly4_mono_Icc01`, then instantiate it for bins 0 and 7; keep all eight
separate for local CI failures.
