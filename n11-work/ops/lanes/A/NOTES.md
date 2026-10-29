SUPERVISOR (2026-10-29 12:20 CST): I cancelled stale CI run 40802064355 (pre-split SHA, 2h+ in) so the queued run on the current head starts. STOP polling the Actions API and re-hashing files each session: that is not progress, and CI takes 30-90 min. Instead do real work: (1) TARGETS.txt trimmed by supervisor to the C450 modules only; SevenClass targets are re-enabled only after C450ChainCompletionMain is green. (2) Meanwhile write offline-checkable math for SevenClass: SevenClassQ0Deg3Cos.lean (cosHiNLag grid monotonicity) per EXPERT, test small pieces in /workspace/tools/mathlib-probe locally with `lake env lean`. (3) Never block waiting for CI; commit what you have.

EXPERT (2026-10-29):
- C450 telescope is sound; keep TARGETS limited to the six C450 files until they are CI-green.
- Remove all SevenClass targets from TARGETS until `C450ChainCompletionMain` is green.
- Do not emit edge/sector proof files before `SevenClassQ0Deg3Mono`, `SevenClassQ0Deg3Bins`, and `SevenClassQ0Deg3EndpointChecks` are green.
- Do not use 2049-case `decide`; add `SevenClassQ0Deg3Cos.lean` proving `cosHiNLag` grid monotonicity.
- Prove each edge by one derivative sign-pair lemma; prove each sector per bin and compare the 8 candidates.
- Keep all Python/static results labeled candidate data, never CI/paid.

SUPERVISOR (2026-10-29 09:45 CST): make `C450ChainCompletion` cheap. The two
pre-split CI runs died after `C450Identify` while loading the 25-deep telescope.
Use several small modules, one `TARGETS.txt` entry each, no giant `decide`/`simp`,
no `native_decide`. Current workflow builds lanes C, B, A and has an OOM guard.

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

## 2026-10-29 (part 32) — exact derivative-sign audit

**Did.** Added a deterministic exact-rational audit of the real derivative route
for `edgeUpper`.  For each of the 21 edges it evaluates
`(19/50)^2 * cosHiNLag(q) - b` at all 2049 grid nodes, where `b = edgeCoeff i`.
All 21 sign patterns align with the recorded peaks: the prefix has nonnegative
slope and the strict suffix has nonpositive slope, including the two peaks at
zero (edges 12 and 13, whose peak slopes are about `-0.18404`).  This gives
finite endpoint data for the monotonicity of the derivative of the real sine
upper bracket, instead of relying on the disproved right-endpoint reduction.

**Files / SHA256.** `n11-work/ops/lanes/A/audit_q0_degree3_edge_derivative.py`
(new) `f6482b608b5f2913257c4ee4e357745ca1ecc436095287bbced5e129d1d28521`;
`n11-work/ops/lanes/A/q0-degree3-edge-derivative.json` (new)
`628a20f6e4758b3a18ccd83215ac23a7e2fabbb11c701bd667a820643b97d726`.
Added `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeReal.lean` (new)
`100a3c1979bbd9f2e0f5cbee18d28a8a365c4552378a92d7df2fbc720a3ce5eb`:
it defines the real bracket, proves
`HasDerivAt (edgeHiReal b) (A*cosHiReal x - b)`, proves
`((edgeUpper b q : ℚ) : ℝ) = edgeHiReal b q` for `0 ≤ q`, and derives
`EdgeDecFrom i` from real antitone behavior and a zero peak.
Input `q0-degree3-piecewise-8.json` has SHA256
`22e49d9dc6962602100f47668ebaaf3d7b3defd3fc126567fbdd7b9084cb6996`.
`TARGETS.txt` now includes `SevenClassQ0Deg3EdgeReal`
(`a2f7d8acbf27ac78e55626a40dd1a1d21f30bb01f5fd370c5fa9a90c9e1793c9`).

**Checks (scope).** `timeout 60 python3 audit_q0_degree3_edge_derivative.py`
exited 0 after the exact `Fraction` scan of 21 × 2049 grid nodes.  It verifies
the exact derivative signs and witness agreement only; it is candidate data,
not a Lean or kernel proof.  A static source scan found no forbidden constructs.
No local Lean build was run; `SevenClassQ0Deg3EdgeReal` is CI-pending.

**Still unproved / unpaid.** All `EdgeIncTo`/`EdgeDecFrom` instances,
`EdgePeakValid`, `SectorValid`, the strict total, `Q0Degree3AreaInput`, the seven
exclusions, and the arbitrary-center theorem remain unproved.  The new real
derivative bridge is drafted but has no kernel status yet.

**Next concrete step.** On the first CI result, repair any kernel errors in
`SevenClassQ0Deg3EdgeReal`, then discharge `edgeDecFrom_of_antitoneOn` for edge
12 (and similarly 13) by proving `cosHiReal x ≤ 1` on the grid range.  Since
`edgeCoeff 12 > (19/50)^2`, this makes the derivative strictly negative and
closes the first two decreasing-suffix obligations.  Do not rerun the full
project locally.

## 2026-10-29 (part 33) — zero-peak edge suffixes: generic reduction + two instances

**Did.** Added `SevenClassQ0Deg3EdgeSuffixHigh.lean`.  Proved
`cosHiReal_le_one` on `[0, RatInterval.piHi]`: on `[0, π/2]` it follows from
`cosHiReal_antitoneOn`; on the rest, the Lagrange bound gives
`cosHiReal x ≤ cos x + 2*x^28/28!`, with `cos x ≤ 0` and the remainder below
`1/2`.  Then proved the generic implication
`(19/50)^2 < b → AntitoneOn (edgeHiReal b) [0, piHi]`, and instantiated it at
edges 12 and 13.  Their exact coefficients are checked by kernel `norm_num`
from `mu`/`tableEdges`; both `EdgeDecFrom 12` and `EdgeDecFrom 13` are drafted.

**Files / SHA256.** `n11-work/lean/N11Formalization/SevenClassQ0Deg3EdgeSuffixHigh.lean`
(new) `ab2c023394b3c70781d5e72a316c078b83c5327f8b44f7992557bc4892c10c32`;
`n11-work/ops/lanes/A/TARGETS.txt` `14853114a1b236e96c0140b5333af9991cc10542cae3e517289b312457732408`
(adds the new target).

**Checks (scope).** Static forbidden-token scan only; no local Lean build was
run.  The new module, including `cosHiReal_le_one`, coefficient comparisons,
and both `EdgeDecFrom` instances, is CI-pending.  Exact candidate data remain
the separate 21 × 2049 derivative-sign audit, not kernel evidence.

**Still unproved / unpaid.** All other `EdgeDecFrom` and all `EdgeIncTo`
instances, all `EdgePeakValid` checks, `SectorValid`, the strict total,
`Q0Degree3AreaInput`, seven exclusions, and the arbitrary-center theorem.

**Next concrete step.** Read the first CI error in `EdgeSuffixHigh`; first repair
`norm_num` unfolding of `edgeCoeff`/`tableEdges` if needed, then reuse the same
`cosHiReal_le_one` argument for every remaining positive-coefficient edge,
while treating zero/negative coefficients by their recorded derivative signs.

## 2026-10-29 (part 34) — high-coefficient suffix scope fixed

**Did.** Added an exact-rational classifier for the high-coefficient suffix
lemma.  It verifies that precisely edges 12 and 13 have `edgeCoeff i > (19/50)^2`
(their coefficients differ by only `1e-35`), so the two Lean instances are the
complete scope of this route.  Edges 0–11 and 14–20 require the other
derivative-sign regimes; extending the lemma to them would be unsound.

**Files / SHA256.** `n11-work/ops/lanes/A/audit_q0_degree3_suffix_threshold.py`
(new) `368893358c9afea5fc13984ce7903bca0a226de6f114805016693221082e378f`;
`n11-work/ops/lanes/A/q0-degree3-suffix-threshold.json` (new)
`97eb19def65af9fbe567645c29a9e62f7e666c40b757395f0b90c30454b11fec`.

**Checks (scope).** `python3 audit_q0_degree3_suffix_threshold.py` exited 0 and
asserted the complete list `[12, 13]`; this is exact finite candidate data, not
a kernel proof.  `SevenClassQ0Deg3EdgeSuffixHigh` remains CI-pending; no local
Lean build was run.

**Still unproved / unpaid.** All other edge shape obligations, both Lean
instances until CI, `SectorValid`, strict total, area input, seven exclusions,
and the arbitrary-center theorem remain open.

**Next concrete step.** On CI, repair `EdgeSuffixHigh` beginning with its first
error; then take edge 11 (largest coefficient below the threshold) and derive
the prefix/suffix crossing from the exact derivative-sign audit rather than
extending the high-coefficient bound.

## 2026-10-29 (part 35) — cosine namespace/coercion repair

**Did.** Repaired `SevenClassQ0Deg3Cos` against the actionable errors in the
last completed CI log (`a201da0d`).  The missing `open` is now explicitly rooted
at `N11Formalization.MetricAreaRationalCertificate`, every `nodeQ` use in the
grid proof is fully qualified, and the rational cast comparison uses
`exact_mod_cast` instead of the stuck `Rat.cast_le.mp` instance search.  The
current source already contained the derivative-algebra repair; no generated or
frozen bytes were edited.

**Files / SHA256.** `n11-work/lean/N11Formalization/SevenClassQ0Deg3Cos.lean`
`abc16decf48b5fbc4bb79a23b07463c4dd6a162a8e5bf7af7e5cee4405f73ee0`;
`n11-work/ops/lanes/A/TARGETS.txt` unchanged
`14853114a1b236e96c0140b5333af9991cc10542cae3e517289b312457732408`.

**Checks (scope).** The tiny Mathlib derivative probe exceeded its local
120-second budget before producing a result; no full-project build was run.
`timeout 120 python3 verify_q0_degree3_cos.py` exited 0: exact rational
monotonicity on all 2048 adjacent steps and a strictly positive final-step gap.
`audit_q0_degree3_edge_derivative.py` exited 0 on all 21 x 2049 derivative
signs, `audit_q0_degree3_edge_unimodal.py` exited 0 on all 21 peaks, and
`audit_q0_degree3_suffix_threshold.py` reproduced exactly `[12, 13]`.  These are
candidate rational checks, not kernel evidence.  Static source scan found no
forbidden constructs.  `Cos`, `EdgeReal`, and `EdgeSuffixHigh` remain
CI-pending.

**Still unproved / unpaid.** `EdgeIncTo`/`EdgeDecFrom` for all 21 edges,
`EdgePeakValid`, all `SectorValid` obligations, the strict total,
`Q0Degree3AreaInput`, the seven exclusions, and the arbitrary-center theorem.

**Next concrete step.** Read the next CI artifact for `Cos` first; if green,
repair the first error in `EdgeReal`, then prove `cosHiReal_le_one` consumers in
`EdgeSuffixHigh`.  Do not rerun the full project locally.
