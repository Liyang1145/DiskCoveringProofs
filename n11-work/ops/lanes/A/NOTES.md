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

Replaced the probe's cap expression for endpoint 0 with the cheaper target
`(19/50 : ℚ) ≤ sinLoNLag (nodeBinAt 0)`.  It still did **not** finish within
45 s in `/workspace/tools/mathlib-probe` (timeout, no diagnostics), so raw
14-term rational unfolding is not a viable endpoint strategy either.  No Lean
project module was built; this is a probe result, not kernel evidence.

For the next attempt, Mathlib's `Real.sin_ge_sub_cube` gives
`sin a ≥ a - a^3/6` for `a ≥ 0`.  A generic bridge
`sinLoNLag a ≥ sin a - 2/29!` (from the degree-29 Lagrange bound and
`sinLoNLag_le_sin`) would reduce every endpoint to
`19/50 + 2/29! ≤ a - a^3/6`, then a short `norm_num` check per endpoint.
Endpoint values all lie in `[0,1]`, so the cubic is positive and gives ample
slack.  The bridge and its use in `SevenClassQ0Deg3EndpointChecks` remain
undrafted.

**Files / SHA256.** `probe_endpoint_normnum.lean` updated (cheap-target probe;
SHA to be refreshed on commit); `TARGETS.txt` unchanged.  Still unproved:
Cos/Bins/EndpointChecks kernel acceptance, then UpperTables premises, strict
total, `Q0Degree3AreaInput`, seven exclusions, arbitrary-center full-disk.

**Next concrete step.** Add `sinLoNLag_lower` beside the existing sine-bracket
lemmas (prefer a new lane module if frozen `IntervalsHighLag` cannot be edited),
prove it via `sin_bound_abs 14` and `sinTQ_cast`, then replace endpoint
`norm_num` definitions with `Real.sin_ge_sub_cube` plus exact per-endpoint
rational checks.

## 2026-10-29 (part 67) — endpoint polynomial reduction drafted

Replaced the eight expensive 14-term `sinTQ`/`sinLoNLag` endpoint expansions by
two reusable kernel-bound routes in `SevenClassQ0Deg3EndpointChecks.lean`:
`sin_bound_abs 4` gives the rational degree-seven lower/upper polynomial with
explicit `1/9!` and `2/29!` losses; `sin_bound_abs 14` converts those into
`sinLoNLag`/`sinHiNLag` bounds. `capQ_le_sinPoly4` then bounds each endpoint cap
without unfolding the 29-term series. This is **drafted, CI pending**, not a
green or paid module. One failed intermediate attempt used the uniform cap
ceiling `19/50` as a lower bound; it was removed. The cubic-only lower bound was
also rejected because the last endpoint missed by roughly `7e-5`; the degree-
seven bound has positive slack there.

**Files / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`5e522766ce46a64f722f1bfa4f4044dce33219c8da02d5695e861eb7dd036656`;
`verify_q0_degree3_endpoint_polynomial.py`
`0859e3b6ec1a3b5d5cfa456b4605b7a6975a7ffbe1420da571ef91edfc8f8a08`;
`q0-degree3-endpoint-poly.json`
`97873a192606db6c150caaf0a5fe406f5475b59406a374a0a1342e790878c8eb`.
`TARGETS.txt` remains `2935e4bd…` and already lists the endpoint module.

**Checks (scope).** The new Python verifier passed all eight exact-rational
comparisons; minimum slack is `1813339696040923404218003961318003972770323 /
52701008282540452209375000000000000000000000000` (about `3.44e-5`).
`git diff --check` and the forbidden-token scan are clean. A narrow
Mathlib-probe compilation of the lower-bound algebra timed out at 140 s on the
2-core sandbox, and no project oleans exist locally, so there is **no Lean
elaboration or kernel evidence yet**. C450 remains CI-green historically.

**Still unproved / unpaid.** Kernel acceptance of the rewritten Cos, Bins and
EndpointChecks modules; their CI run is pending. Then UpperTables
edge/sector premises, strict total, `Q0Degree3AreaInput`, all seven exclusions,
and the arbitrary-center full-disk theorem remain open.

**Next concrete step.** Supervisor commit this endpoint rewrite and let CI run
the existing five lane-A targets. If EndpointChecks is red, repair only the
first reported proof line; if green, promote the UpperTables dependency in
`TARGETS.txt` and inspect its three explicit premise families.
