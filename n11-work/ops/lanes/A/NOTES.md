EXPERT (2026-10-30):
- C450 is closed: 36/36 green and transitively imported via EnergyTerminalBatchB12Main. Do no more C450 proof work.
- Highest leverage: split EndpointChecks domains. `endpointUBin 5/6/7 > 1` and `nodeQ_binHi 5/6/7 > 2`; the all-bin quartic bridge is false.
- Keep `capQ_le_sinPoly4_of_u_le` only for bins 0–4; delete or restrict `endpointUBin_le_one` and `nodeQ_binHi_le_two`.
- Bins 5–6: `capQ_mono` + `sinHiNLag_mono` to `11774/10000` and `13737/10000`; close `capQ (2*u)` against `sinLoNLag (nodeBinAt j)` by `norm_num`.
- Bin 7: `piHiCapSaturated` gives cap `19/50`; prove `19/50 ≤ sinLoNLag (1949/5000)` directly by `norm_num`.
- Then require CI 0 in order Cos, Bins, EndpointChecks. Current repairs are pending, not paid.
- Q0 degree 3 remains unpaid after endpoints: EdgeValid, SectorValid, strict total, certificate construction, and Q0Degree3AreaInput are still open.

# Lane A notes

## Directives and ledger

- See the EXPERT (2026-10-30) block above for current directives.
- SUPERVISOR: stop polling Actions/re-hashing; work offline and never block on CI.
- C450 chain: CI-green at `495c970c` and transitively imported through
  `EnergyTerminalBatchB12Main`; only the stale `HARK-MISSING` comments remain.
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

Added `sinPoly4Real`, its derivative bound, and `sinPoly4_mono_Icc01` to
EndpointChecks, enabling low-denominator endpoint caps.  No project oleans were
available locally; status was **drafted, CI pending**.  (Superseded by part 9.)

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

## 2026-10-30 (parts 11–12) — cap audit corrected; analytic margin isolated

Found and fixed a double-counting defect in `verify_piHi_cap.py`: `sinHiNLag`
is `sinTQ 14 + x^29/29!`, but the old script summed 15 Taylor terms **and**
added that remainder.  Corrected the range to 14.  The true exact margin is
`sinHiNLag(piHi/2) - 1 = 1.4577417234587796e-28`; the previously recorded
`5.52e-26` was inflated by one extra degree-29 term.  The exact comparison
still PASSES.

A 90-second bounded Mathlib probe of the old monolithic
`norm_num [sinTQ, Finset.sum_range_succ, piHi]` proof timed out, so that route
is not CI-viable.  Added `verify_piHi_cap_analytic.py`, which checks the margin
for a non-expansion proof via `sinHiNLag = sinT 15`, the Taylor-16 remainder,
`sin(pi/2+d) = cos d >= 1-d^2/2`, and `d < 1/(2*10^20)`: Taylor-31 lower term
`3.4636120574858e-29` exceeds the cosine-deficit allowance `1.25e-41` by a
factor `2.77e12` (PASS).  This is exact-rational candidate data, not kernel
evidence.

**Files / SHA256.** Cos `fa245b343adbf598b44a14af6cf177f3bb22fcd35e418f951cc2d58d14b22971`;
Bins `7a5ba5e05aa7f5e96a9dd3991372df1bc1bc70d95b90224281cc4226811fbbf7`;
`verify_piHi_cap.py` `d77a84e363341c933d95701db3de27c5d4f8768916f0b1edde3b107df66ac372`;
`verify_piHi_cap_analytic.py` `a7606ff6fd1d603348732ef312a32a2adf7f9a18f17812b3de29a3ed713e7b1e`.

**Checks (scope).** Corrected cap audit PASS; analytic-margin audit PASS;
`git diff --check` clean.  The local bounded probe re-ran the old expansion and
timed out at 90 s; no project module was elaborated.  CI `40983359848` predates
the current Bins/Cos repairs (old Cos `No goals`, old Bins `hjlt` mismatch), so
those diagnostics are historical.  Cos/Bins/EndpointChecks remain **drafted,
CI pending**.

**Still unpaid.** Kernel acceptance of Bins/Cos/EndpointChecks; the analytic cap
lemma; `EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  C450 root import remains a
supervisor action.

**Next concrete step.** In Bins, prove `sinHiNLag q = sinT 15 q` (cast), derive
`sinT 15 x >= Real.sin x - x^33/33! + x^31/31!` from `sin_bound_abs 16`, then
instantiate the rational bounds checked above.  Keep `piHiCapSaturated` as the
only consumer and do not change the cap statement.

## 2026-10-30 (part 13) — Bins CI diagnostics repaired

CI `40988698121` gives the first current Bins failures at `SevenClassQ0Deg3Bins.lean:85`
(`split` found no splittable conditional) and `:114` (over-specified
`exact_mod_cast`).  Replaced the conditional grid-index proof with an explicit
`Nat.div_add_mod`/remainder argument, and replaced the cast step by
`Rat.cast_le.mpr` followed by transitivity with `pi_div_two_lo_lt.le`.  Cos line
`205` is the historical `exact le_rfl`; the worktree already replaces it by
`simpa [gridCos, h1]` (drafted, CI pending).

**Files / SHA256.** Bins `ac894d68823b12a083a9b08c079ae7571124c057c66d9694bdf2820d34f14381`;
Cos `fa245b343adbf598b44a14af6cf177f3bb22fcd35e418f951cc2d58d14b22971`;
EndpointChecks `fddea8134398beab87c846a454dd76f8e6102352edbaead25cf260740ddf53b9`;
`verify_piHi_cap.py` `d77a84e363341c933d95701db3de27c5d4f8768916f0b1edde3b107df66ac372`;
`verify_piHi_cap_analytic.py` `a7606ff6fd1d603348732ef312a32a2adf7f9a18f17812b3de29a3ed713e7b1e`;
`audit_endpoint_low_denom.py` `c5e41aa104562b949853cd74175e9361b5255e2a856cdb3f05fde13aae4e2157`.

**Checks (scope).** Endpoint audit PASS 8/8, minimum slack `3.44080645729e-5`;
cap audit PASS with exact positive slack; analytic-margin audit PASS;
`git diff --check` and forbidden-token scan clean.  A trivial local Lean file
eventually ran, but no project module was elaborated because project `.olean`
files are absent.  Bins/Cos/EndpointChecks remain **drafted, CI pending**.

**Still unpaid / next step.** Kernel acceptance of Cos, Bins, EndpointChecks;
`EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  On next CI, read Bins first;
only if Bins is green read the first EndpointChecks diagnostic.  Do not change
the endpoint statements.
