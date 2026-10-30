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

## Earlier ledger (condensed)

- `UpperTables` has 21 edge and 9 sector obligations.  The first right-endpoint
  reduction was disproved at edge 12 (`0.17097552… > (19/50)^2`); the unimodal
  wrapper and 21 exact peaks remain, but no Lean premise proof exists.
- Cos/Mono repairs use explicit rational-min casts and `ring_nf`; C450 plus all
  five completion modules were CI-green at `40914236268`.  EdgeReal/high-suffix
  modules are off the critical target list.
- Exact-rational audits passed for 2048 cosine steps, `piHi` cap, eight bin
  maxima, 21×2049 edge derivatives, and the q0 area/hub graph.  Candidate data
  only; project `.olean` files are absent locally.

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

## Earlier Condensed (parts 10--13)

- Migrated all eight endpoint bins to low-denominator bridges and repaired
  early Bins/Cos CI diagnostics.  CI `40988698121` predates these fixes, so
  those error lines are historical; see hashes below.
- Corrected `verify_piHi_cap.py` double counting: exact margin is
  `1.4577417234587796e-28`, still positive.  The 90-second monolithic
  `norm_num` probe timed out on the old expansion.
- Added the analytic cap-margin audit; endpoint audit PASS 8/8 with minimum
  slack `3.44080645729e-5`.  Candidate data only, not kernel evidence.
## 2026-10-30 (part 14) — false high-bin premise removed

Static audit found a genuine defect in `EndpointChecks` independent of the old
CI diagnostics: bins 5--7 have `nodeQ(binHi j) > 2`, so
`nodeQ_binHi_le_two` was false and the `[0,1]` degree-seven bridge did not apply.
Replaced bins 5--6 with `sinHiNLag_le_sinPoly4_add_pow`, keeping the degree-nine
and degree-29 Taylor remainders, followed by an exact degree-seven endpoint
comparison.  Bin 7 now uses the existing saturated theorem
`piHiCapSaturated : capQ piHi = 19/50` and a rational `sinLoNLag` lower bound.
Bins 0--4 are unchanged.  The endpoint statement itself is unchanged.

**Files / SHA256.** EndpointChecks
`80cd40078a0ebdd8c18fda0a497b7dfdce60fef8a7a649f302644880477d85d2`;
audit `2956cc05a49f342c08c356b6a7d52f34c39fb9dfef23a8f7cd8216649064e957`;
TARGETS `500cc3707072af67a662fb6d14a5636560ccf462ae3a9f990f0e75350e01fbf4`.

**Checks (scope).** Exact-`Fraction` audit PASS 8/8 on the split branches;
slacks: bins 5/6 `1.8550729002e-4` / `1.32553652856e-4`, bin 7 `6.6940497252e-7`.
`git diff --check`, forbidden-token scan clean.  No project module was elaborated:
the local project `.olean` cache is absent.  EndpointChecks is **drafted, CI
pending**; this repair is not kernel-paid evidence.

**Still unpaid / next step.** Kernel acceptance of EndpointChecks (then Bins and
Cos); `EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  On next CI read the first
EndpointChecks diagnostic; if green, read Bins, then Cos.  Do not weaken the
endpoint statement or reuse the withdrawn `q ≤ 2` premise.

## 2026-10-30 (part 15) — lower endpoint proof repaired

Static review found that `sinLoNLag_ge_sinPoly4_sub` used two lower Taylor
remainder bounds and then asked `linarith` for a conclusion those hypotheses
cannot imply.  Replaced it by the direct alternating-tail argument: added
`sinTaylorPair_le` (each adjacent odd term decreases on `[0,1]`) and
`sinPoly4_le_sinTQ14` (the degree-9 through 27 tail is nonnegative).  The
degree-29 remainder is then bounded by `1/29!`.  Statement unchanged.

**Files / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`defc4c5be09bbd91aa4bea6bf9006ceb026a4c1b4c9fdfa76a7afcf562d0f6fd`;
`audit_endpoint_low_denom.py`
`2956cc05a49f342c08c356b6a7d52f34c39fb9dfef23a8f7cd8216649064e957`.

**Checks (scope).** Exact-`Fraction` endpoint audit PASS 8/8 (minimum slack
`6.6940497252e-7` at bin 7); `git diff --check` and forbidden-token scan
clean.  A bounded isolated Lean probe could not elaborate: the local Mathlib
package has only the stub `Mathlib.olean`, not
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.olean`.  No project
module was kernel-checked locally.  EndpointChecks is **drafted, CI pending**.

**Still unpaid.** Kernel acceptance of EndpointChecks, Bins and Cos;
`EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  C450 root import remains a
supervisor action.

**Next concrete step.** On the next CI report read the first EndpointChecks
diagnostic; if green read Bins, then Cos.  Do not weaken the endpoint
statement or reuse the withdrawn `q <= 2` premise.
