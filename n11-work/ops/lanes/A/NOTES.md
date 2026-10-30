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

## 2026-10-30 (parts 7--9) — endpoint bridge (condensed)

Exact endpoint audits passed 8/8.  Added `sinPoly4Real`, derivative
monotonicity, `capQ_le_sinPoly4_of_u_le`, the eight `endpointUBin` constants,
and their exact node bounds.  The polynomial bridge replaces large `piHi`
expansions; statements were unchanged.  All results in this block were
**drafted, CI pending**, and no project Lean module was locally elaborated.

## Earlier Condensed (parts 10--13)

- Migrated all eight endpoint bins to low-denominator bridges and repaired
  early Bins/Cos CI diagnostics.  CI `40988698121` predates these fixes, so
  those error lines are historical; see hashes below.
- Corrected `verify_piHi_cap.py` double counting: exact margin is
  `1.4577417234587796e-28`, still positive.  The 90-second monolithic
  `norm_num` probe timed out on the old expansion.
- Added the analytic cap-margin audit; endpoint audit PASS 8/8 with minimum
  slack `3.44080645729e-5`.  Candidate data only, not kernel evidence.
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

## 2026-10-30 (part 16) — false universal endpoint premises removed

Re-audited `SevenClassQ0Deg3EndpointChecks.lean` after the split-domain
repair.  Three helper statements still quantified over all `Fin 8`:
`endpointUBin_le_one`, `nodeQ_binHi_le_two`, and their consumer
`capQ_binHi_le_endpointUBin`.  They are false at bins 5--7, so the claimed
universal bridge was not a valid proof path even though bins 5/6 and bin 7
already had separate proofs.  Restricted all three helpers to `j.val < 5`
and passed the proof at each of the five call sites.  Bins 5--6 remain on the
explicit degree-9/degree-29 remainder branch; bin 7 remains on
`piHiCapSaturated`.  The public `EndpointCheck`/`EndpointValid` statements are
unchanged.

**Files / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`4cb57028465dae98975045beb8ff7d6eca4fadae46662060c15d1bcafae522a2`;
`audit_endpoint_low_denom.py`
`2956cc05a49f342c08c356b6a7d52f34c39fb9dfef23a8f7cd8216649064e957`.
No new module; `TARGETS.txt` remains unchanged.

**Checks (scope).** Exact-`Fraction` endpoint audit PASS 8/8, minimum slack
`6.6940497252e-7` at bin 7.  `git diff --check`, forbidden-token scan, and
`python3 tools/project_status.py --check` (handoff index only) pass.  No local
project Lean elaboration: the worktree lacks project oleans.  EndpointChecks
is **drafted, CI pending**, not paid.

**Still unpaid.** Kernel acceptance of EndpointChecks, Bins and Cos;
`EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  C450 is already CI-green but
its unchanged root import remains a supervisor action.


## 2026-10-30 (part 17) — upstream Bins/Cos diagnostics repaired

Made the stale `2fdf1a1c` diagnostics actionable: `Cos` now closes the
unchanged final grid step with `simpa [gridCos, h1]` instead of the redundant
`rw; exact le_rfl`; `Bins` no longer relies on `split` for either projection
of `binHi (binIndex k)`, using explicit `by_cases`/`hval` rewrites and an
explicit rational cast for the `piLo/2` transfer.  The endpoint split-domain
repair is unchanged.  All three modules remain **drafted, CI pending**.

**Files / SHA256.** EndpointChecks `4cb57028465dae98975045beb8ff7d6eca4fadae46662060c15d1bcafae522a2`;
Bins `b997ee8dbfdb0c7b77dbe6ebde77e665ca2fcb1b018de8ec3adfee425f895584`;
Cos `fa245b343adbf598b44a14af6cf177f3bb22fcd35e418f951cc2d58d14b22971`;
TARGETS `500cc3707072af67a662fb6d14a5636560ccf462ae3a9f990f0e75350e01fbf4`.

**Checks (scope).** Endpoint exact-`Fraction` audit PASS 8/8 (minimum slack
`6.6940497252e-7`, bin 7); `project_status.py --check`, `git diff --check`,
and forbidden-token scan pass.  No local project kernel check: the worktree
has no N11 oleans, and a bounded broad-Mathlib probe timed out before
elaboration.  CI exit 0 is still required.

**Still unproved.** Kernel acceptance of Cos, Bins, EndpointChecks;
`EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  C450 is CI-green.

**Next step.** After supervisor push, read CI in order Cos, Bins,
EndpointChecks; fix the first new source diagnostic rather than weakening a
statement.  ROOT-IMPORT REQUEST remains for C450ChainCompletionMain.

## 2026-10-30 (part 18) — Taylor product comparison corrected

Static audit of the part-15 alternating-tail proof found its denominator
clearing step used `mul_le_mul_of_nonneg_left`, which cannot produce the needed
product inequality.  `sinTaylorPair_le` now uses `mul_le_mul` with both
`a^(n+2) <= a^n` and `n! <= (n+2)!`, hence proves
`a^(n+2)*(n!) <= a^n*((n+2)!)` after `div_le_div_iff`.  Statement unchanged.

**Files / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`37215ea7b528a37b08fbb3d708ff39ee2a95323b9d7436e9ddcd77e44cd46fd5`.

**Checks (scope).** Endpoint exact-`Fraction` audit PASS 8/8; tightest slack
`6.6940497252e-7` at bin 7.  `git diff --check` and
`python3 tools/project_status.py --check` pass.  No local project Lean build:
the N11 worktree has no project oleans.  EndpointChecks remains **drafted, CI
pending**, not kernel-paid.

**Still unproved.** Kernel acceptance of EndpointChecks, Bins and Cos;
`EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  C450 is CI-green; its root
import remains a supervisor action.

**Next concrete step.** On the next CI report read the first EndpointChecks
diagnostic, then Bins and Cos; repair the exact failing source line without
weakening any statement.

## 2026-10-30 (part 19) — first real CI diagnostic repaired

Run `40998371772` (head `88918335`) built C450Main, Cos and Mono at exit 0,
but Bins was exit 1 and EndpointChecks only failed as its dependency.  Bins
line 87 used unavailable `le_or_lt`; the resulting metavariable also broke
the following `Nat.mod_lt` proof.  Replaced it with explicit `by_cases` and
`Nat.lt_of_not_ge` (Bins hash
`1a880281e01e8152891596e1a097773b8d4ebb43c4055ab94aad6f27a54a6412`).

Static audit also found `sinHiNLag_le_sinPoly4_add_pow` could not derive the
`sinT 14` upper tail from `sin_bound_abs 4`.  It now uses
`sinLoNLag_le_sin : sinT14 - r29 <= sin`, combined with the degree-4 upper
remainder, to prove `sinT14 + r29 <= sinPoly4 + r9 + 2*r29`.  EndpointChecks
is **drafted, CI pending**, hash
`57a9d28dc9c9b7f0787ee0e587651be26d8ad71cb7fd17bf6f0bf8c514ec6cee`.

**Checks (scope).** `project_status.py --check`, `git diff --check`, and the
forbidden-token scan pass.  No local project elaboration: N11 oleans are
absent; the Mathlib probe timed out during import.  No kernel payment claimed.

**Still unpaid.** Bins and EndpointChecks kernel acceptance;
`EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  ROOT-IMPORT REQUEST remains
for `C450ChainCompletionMain`.

**Next concrete step.** Push and read CI in order Bins, then EndpointChecks;
fix the first new source diagnostic without weakening a statement.  If both
are green, connect `allNodeValid` to the area certificate and attack
`EdgeValid`/`SectorValid`.

## 2026-10-30 (part 20) — bins 5/6 use monotonicity + concrete endpoints

The part-19 generic `sinHiNLag_le_sinPoly4_add_pow` repair was still
mathematically unsound: a lower bound on `sin` cannot upper-bound the
`sinT 14` tail.  Removed that lemma.  Bins 5/6 now use the already-proved
`sinHiNLag_mono` on `[0, π/2]` to transfer from `q/2` to the explicit
`endpointUBin`, then evaluate `sinHiNLag (endpointUBin) ≤ endpointUpperBin`
by one concrete rational `norm_num` each.  No node-dependent degree-29
expansion remains.

**Files / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`9ac5c7239f4bd84310cc2865f376b2525e57f1765295fd05e9614b0abf51c86c`;
`audit_endpoint_low_denom.py`
`a2db7f96514248db74122eb7845cdce5fbd700667ec620fbeb088678d62cbf1f`.

**Checks (scope).** Exact-`Fraction` endpoint audit PASS 8/8, including the
new monotone endpoint-pair check and `sinHiNLag ≤ endpointUpperBin`; minimum
overall lower slack `6.6940497252e-7` (bin 7), bins 5/6 slack
`1.75347e-4`/`1.31050e-4`.  `project_status.py --check`, `git diff --check`,
and forbidden-token scan pass.  No local project kernel check (N11 oleans
absent); this is **drafted, CI pending**, not paid.

**Still unpaid.** Kernel acceptance of Cos, Bins, EndpointChecks;
`EdgeValid`/`SectorValid`; strict total; `Q0Degree3AreaInput`; all seven
exclusions; arbitrary-center full-disk theorem.  C450 root import remains a
supervisor action.

**Next concrete step.** Read the new CI diagnostics in order Cos, Bins,
EndpointChecks; if green, connect `allNodeValid` to the q0 area certificate
and attack `EdgeValid` or `SectorValid`.
