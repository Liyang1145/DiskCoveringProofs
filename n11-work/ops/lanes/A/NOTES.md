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

## Condensed ledger through 2026-10-30 part 3

- Latest CI `40973981403` (`76b6835e`): C450Main exit 0 (telescope green); Cos
  exit 1 at old line 203; Bins exit 1 at lines 64/81; EndpointChecks exit 1;
  root OOM in unrelated `SharedMomentConcreteSwitchBatch`.
- Cos current source has explicit natural/rational cast witnesses and is
  **drafted, CI pending**; do not reuse its old line numbers as current failures.
- Exact `piHi` degree-29 `norm_num` endpoint probes timed out at 100--150 s.
  Low-denominator `u_j` checks and the eight-bin max audit pass as Python data.
- Historical C450/Mono evidence is green; the C450 root import is still a
  supervisor action.  Python/static checks never count as kernel evidence.
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

## 2026-10-30 (part 9) — low-denominator endpoint bridge implemented

Added `capQ_le_sinPoly4_of_u_le`, eight `endpointUBin` constants, nonneg/≤1 and
exact `nodeQ(binHi j)/2 ≤ endpointUBin j` lemmas, plus
`capQ_binHi_le_endpointUBin`.  Replaced the huge exact-`piHi` polynomial
comparison in `endpointCheck_0` and `endpointCheck_7` with this bridge; bins
1--6 still use the old proof shape.  This changes proof cost, not the statement.

**File / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`eecc3457e47c9202dd026bd12425f00f41c0952bfa5e786f4c0d275275514b42`.
EndpointChecks is already in `TARGETS.txt`; no new module/target.

**Checks (scope).** `audit_endpoint_low_denom.py` PASS, 8/8 exact rational
comparisons, minimum slack `3.44080645729e-5`;
`verify_q0_degree3_endpoint_polynomial.py` PASS, same exact minimum slack.
`git diff --check` and forbidden-token scan clean.  No local Lean elaboration:
the worktree has zero project oleans and the Mathlib probe has only a stub.
Status is **drafted, CI pending**, not green or paid.

**Still unproved / unpaid.** Kernel acceptance of Cos, Bins, EndpointChecks;
low-denominator migration for bins 1--6; `EdgeValid`/`SectorValid` premises;
strict total; `Q0Degree3AreaInput`; all seven exclusions; arbitrary-center
full-disk theorem.  C450 root import remains requested but unperformed.

**Next concrete step.** Supervisor commit/push, then read the first EndpointChecks
CI diagnostic.  If bins 0/7 pass, migrate bins 1--6 identically; separately repair
Bins lines 64/81 and the current first Cos line.  Do not alter frozen/toolchain/root.

## 2026-10-30 (part 10) — all eight endpoint bins migrated; Bins diagnostics repaired

Migrated endpoint checks 1--6 to the low-denominator `endpointUBin` bridge, so all
eight bins now share the degree-seven monotonicity proof shape.  Removed Bins'
unused `hjlt` binding (the CI type-mismatch site).  Rewrote the `piHiCapSaturated`
proof to discharge `0 ≤ piHi/2` explicitly and rewrite `|piHi/2| = piHi/2`
before the 15-term `norm_num` expansion.  This targets the old unsolved-goal
failure; shortening `piHi` is impossible because the exact cap margin is only
about `5.52e-26` (also `piLo/2` gives the same positive margin).

**Files / SHA256.** `SevenClassQ0Deg3Bins.lean`
`7a5ba5e05aa7f5e96a9dd3991372df1bc1bc70d95b90224281cc4226811fbbf7`;
`SevenClassQ0Deg3EndpointChecks.lean`
`fddea8134398beab87c846a454dd76f8e6102352edbaead25cf260740ddf53b9`;
`audit_endpoint_low_denom.py`
`c5e41aa104562b949853cd74175e9361b5255e2a856cdb3f05fde13aae4e2157`;
`verify_piHi_cap.py`
`516cf72873468d9fdbdf39a564d7fa4a6c870773e1089ba68d6a1f5859b4064d`;
`TARGETS.txt`
`500cc3707072af67a662fb6d14a5636560ccf462ae3a9f990f0e75350e01fbf4`.

**Checks (scope).** `git diff --check` clean; forbidden-token scan clean for both
touched Lean files; `audit_endpoint_low_denom.py` PASS 8/8 exact rational
comparisons (minimum slack `3.44080645729e-5`); `verify_piHi_cap.py` PASS with
positive exact cap slack.  No local project Lean elaboration (no project oleans;
Mathlib probe has only the stub `Mathlib.olean`).  Bins/Cos/EndpointChecks remain
**drafted, CI pending**; nothing here is kernel-paid evidence.

**Still unproved / unpaid.** Kernel acceptance of Cos, Bins, EndpointChecks;
`EdgeValid`/`SectorValid` premises; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  C450 root import still requested.

**Next concrete step.** After supervisor push, read the Bins CI diagnostic first.
If the cap line still fails, isolate `sinHiNLag (piHi/2)` in a small Mathlib probe
and split the 15-term expansion into named partial sums; if Bins is green, read
the first EndpointChecks diagnostic and repair only that bin.

## 2026-10-30 (part 11) — resumed checkpoint; audits re-run

Re-read the part-10 source state and re-ran the two candidate-data checks.
`audit_endpoint_low_denom.py` passed all eight exact rational upper caps
(minimum slack `3.44080645729e-5`); `verify_piHi_cap.py` passed with positive
exact slack for `sinHiNLag(piHi/2) > 1`. `git diff --check` and the forbidden
token scan are clean. File hashes are unchanged from part 10: Bins
`7a5ba5e05aa7f5e96a9dd3991372df1bc1bc70d95b90224281cc4226811fbbf7`,
EndpointChecks `fddea8134398beab87c846a454dd76f8e6102352edbaead25cf260740ddf53b9`.

**Scope / status.** These are Python exact-rational checks and static hygiene,
not Lean kernel evidence. Bins and EndpointChecks remain **drafted, CI pending**.
No local project elaboration was attempted. Cos is likewise drafted/CI pending;
`EdgeValid`, `SectorValid`, strict total, `Q0Degree3AreaInput`, all seven
exclusions, and the arbitrary-center theorem remain unpaid.

**Next concrete step.** On the next CI result, read Bins first (part-10 cap-line
diagnostic); if it is green, read EndpointChecks at its first failing bin. Do not
change the eight endpoint statements; only repair the failed proof step.
