EXPERT (2026-10-30 07:19 UTC):
- C450 stays closed (36/36, root-reachable through B12Main); make no C450 edits.
- The new `hbhi` branch under outer `h7` is correct, but Bins is still red at line 95: `Nat.mod_lt k.val (by norm_num)` leaves `⊢ 0 < ?m`.
- Fix that leaf with an explicit modulus, e.g. `Nat.le_of_lt (Nat.mod_lt k.val (n := 256) (by norm_num))`; do not add another case split.
- EndpointChecks has no independent verdict until Bins is green; preserve its restricted 0–4 plus separate 5/6/7 branches.
- Require module exits 0 in order Cos, Mono, Bins, EndpointChecks, UpperReductionUnimodal; the completed run predates the current Bins and peak bytes.
- `edgePeakValid_*` is genuine 21-way peak credit, not float/manifest credit; `EdgeMonotone` remains the only gap to EdgeValid.
- After green, prove full-angle `cosHiNLag_nodeQ_antitone`; the existing `cosHiNLag_grid_antitone` is half-angle and cannot pay edge derivatives, especially witnesses 9/10 at 1489.
- Split 42 derivative leaves into `SevenClassQ0Deg3EdgeShape.lean`; start with edge 9 as the full-angle template, then `SectorValid`, strict total, and `Q0Degree3AreaInput`.
- SevenClassExclusions remains 0/7; no edge/peak table alone pays a class.

# Lane A notes

## Directives and ledger

- See the EXPERT (2026-10-30) block above for current directives.
- SUPERVISOR: stop polling Actions/re-hashing; work offline and never block on CI.
- C450 chain: CI-green at `495c970c` and transitively imported through
  `EnergyTerminalBatchB12Main`; only the stale `HARK-MISSING` comments remain.
- Seven-class: 0/7 exclusions paid.  q0 degree three has exact-rational candidate
  data, but no kernel green all-node certificate.  Energy/B13 are lane B; the
  arbitrary-center full-disk theorem remains open.

## Consolidated earlier ledger (through 2026-10-30 part 13)

- C450 plus five completion modules were CI-green at `40914236268`; the
  portable telescope audit later passed 25/25 transfers, both terminal facts,
  and 26/26 drop/count rows.  Python/static checks are not kernel evidence.
- `UpperTables` still has 21 edge and 9 sector obligations.  The right-endpoint
  reduction fails at edge 12 (`0.17097552… > (19/50)^2`), so no Lean premise
  proof exists even though the unimodal wrapper and exact peaks are present.
- Exact-rational audits cover 2048 cosine steps, the `piHi` cap, eight bin
  maxima, 21×2049 edge derivatives, and the q0 area/hub graph.  Corrected cap
  margin is `1.4577417234587796e-28`; endpoint slack was then `3.44080645729e-5`.
- CI `40973981403` (`76b6835e`) had C450Main exit 0, but Cos/Bins/Endpoint red
  and the root OOM in unrelated `SharedMomentConcreteSwitchBatch`.  Old line
  numbers are not current diagnostics.  Project `.olean` files are absent.

## Consolidated 2026-10-30 parts 15--23 (superseded detail)

- EndpointChecks was repaired across several diagnostics: the lower Taylor
  remainder now uses the direct alternating-tail argument; false universal
  `Fin 8` endpoint premises were restricted to bins 0--4; and bins 5/6 use
  explicit rational endpoint constants, with bin 7 on `piHiCapSaturated`.
  Exact endpoint audit PASS 8/8, minimum slack `6.6940497252e-7` (bin 7).
- Cos and Mono were CI-green at `e5875cf8`.  Bins received two source repairs:
  unavailable `le_or_lt` was replaced by `by_cases`; then the redundant inner
  split after the outer `h7` was removed and `binHi` rewritten with
  `simp [binHi, h7]`.  The structural bin audit passes 2049/2049.  Bins source
  SHA256 is `b336488ab942bcfd08f0defef168190d66ac6dea9e6580be09cc88dc6bca379c`;
  it is **drafted, CI pending**, not paid.
- `SevenClassQ0Deg3UpperReductionUnimodal.lean` introduced `EdgeMonotone`
  (42 analytic shape facts), exact edge witnesses, and the finite-peak
  reduction `edgeValid_of_unimodal`.  The earlier aggregate 21-case
  `norm_num` was replaced in part 23 by 21 separate peak theorems plus a
  `fin_cases` dispatcher, avoiding one oversized kernel check.
- Exact `Fraction` `audit_q0_degree3_edge_unimodal.py` PASS 21/21 (witnesses
  and maxima agree; JSON SHA256
  `2a0a38b150cae0b9d200c90f273084b3bdbd4f51d43f4eca1270d8ea5b2f412f`).

## 2026-10-30 (part 23) — edge peak checks split

Split `edgePeakValid_all` into `edgePeakValid_0` … `edgePeakValid_20`, each a
single exact rational comparison, and dispatch the universal theorem by
`fin_cases i <;> first | exact edgePeakValid_n`.  Statement and table data are
unchanged.  This is a CI-resource hardening, not a new mathematical premise.

**File / SHA256.** `SevenClassQ0Deg3UpperReductionUnimodal.lean`
`f31832c0562f3ee46478a8592ef9be9a07cd22a0e987bf422a510d046dc59748`.
`TARGETS.txt` already requests the module.

**Checks (scope).** `project_status.py --check`, `git diff --check`, and the
forbidden-token scan pass.  Exact edge audit PASS 21/21.  `gh` is unavailable;
`ops/ci/LATEST.md` is stale, so no current kernel result exists.  All Lean
items remain **drafted, CI pending**: Bins, EndpointChecks, and
UpperReductionUnimodal.

**Still unproved.** Kernel acceptance of Bins, EndpointChecks and
UpperReductionUnimodal; the 42 `EdgeMonotone` facts; all 9 sectors; strict
total; `Degree3AreaCertificate`/`Q0Degree3AreaInput`; all seven exclusions;
the arbitrary-center full-disk theorem.  C450 is closed; no C450 edits.

**Next concrete step.** On CI, read Bins first, then EndpointChecks, then
UpperReductionUnimodal; fix the first source diagnostic without weakening a
statement.  If the edge module is green, prove one `EdgeIncTo`/`EdgeDecFrom`
case from the cosine derivative as the template for all 42 facts.

## 2026-10-30 (part 4) — edge audits re-run; domain obstruction identified

Re-ran the exact `Fraction` audits against the current edge data.
`audit_q0_degree3_edge_unimodal.py` reports PASS 21/21 with JSON SHA256
`2a0a38b150cae0b9d200c90f273084b3bdbd4f51d43f4eca1270d8ea5b2f412f`;
`audit_q0_degree3_edge_derivative.py` reports exact derivative signs aligned
for 21/21 edges with JSON SHA256
`628a20f6e4758b3a18ccd83215ac23a7e2fabbb11c701bd667a820643b97d726`.
`git diff --check` and the forbidden-token scan over the two changed Lean
files pass.  CI `LATEST.md` contains only the earlier in-progress run
`41008974701` at `43b1d43f`; it predates these sources, so kernel status is
still **CI pending**, not green.

Current source hashes: Bins
`b336488ab942bcfd08f0defef168190d66ac6dea9e6580be09cc88dc6bca379c`;
UpperReductionUnimodal
`f31832c0562f3ee46478a8592ef9be9a07cd22a0e987bf422a510d046dc59748`;
TARGETS
`41c1aca5a3466586249928a1d6bacf1adeaeb3c923f7e568b39febb0fbfdda80`.

**New technical finding.** Edges 9 and 10 have `edgeWitness = 1489`, i.e.
the witness angle is about `2.284 > π/2`.  The existing
`cosHiReal_antitoneOn` only covers `[0, π/2]`, so it cannot alone prove the
monotone prefix for those edges.  The next proof must first extend the upper
cosine bracket's antitonicity through `RatInterval.piHi` (equivalently prove
the degree-27 Taylor sine lower bracket nonnegative there), or split the
prefix at `π/2` and supply the second-interval comparison.

**Still unproved.** Kernel acceptance of Bins, EndpointChecks and
UpperReductionUnimodal; all 42 `EdgeIncTo`/`EdgeDecFrom` facts; all 9 sectors;
strict total; `Degree3AreaCertificate`/`Q0Degree3AreaInput`; all seven
exclusions; the arbitrary-center theorem.

**Next concrete step.** Extend `cosHiReal_antitoneOn` to
`Set.Icc 0 (RatInterval.piHi : ℝ)` by proving `sinT 14 x ≥ 0` on that interval,
then instantiate the first edge's two derivative-sign checks as templates.

## 2026-10-30 (part 5) — negative-coefficient suffix route for edges 9/10

**Files.** Added `N11Formalization/SevenClassQ0Deg3EdgeSuffixNonpos.lean`
(SHA256 `81fcc16d461914bea2813efe7a5f5c80e017d711d8746459c342c663610a1ee8`)
and appended its target to `TARGETS.txt` (SHA256
`f17769f1b31723b4280df3dd8cff470db3a3060594eb45bae0da12595927fd54`).
No frozen module was edited.

**Mathematics drafted.** Corrected the part-4 obstruction: forcing
`cosHiReal_antitoneOn` through all of `piHi` is not required. For edges 9 and
10 the edge coefficient is negative. On the suffix beginning at grid witness
1489, `x ≥ 2π/3`; a cosine lower-sign estimate gives `cos x ≤ -1/2`, the
factorial Taylor remainder gives `cosHiReal x ≤ 0`, and hence
`A * cosHiReal x - b < 0` because `b < 0`. This proves decreasing suffixes for
both edges via `edgeHiReal_antitoneOn_of_coeff_neg` and the witness-relative
dispatcher `edgeDecFrom_of_antitoneOn_from`.

**Checks (scope).** `project_status.py --check`, `git diff --check`, and a
forbidden-token scan over the new module pass. These are static checks only.
The new module is **drafted, CI pending**; no local project build was run.
The exact suffix-threshold audit remains `covered_edges = [12,13]`; this new
route is separate and its coefficient/witness facts are Lean obligations, not
inferred from that audit.

**Still unproved.** Kernel acceptance of the new module and all previously
listed lane-A targets; increments for the remaining 17 increasing prefixes,
the other 17 decreasing suffixes, all 9 sectors, strict total,
`Degree3AreaCertificate`/`Q0Degree3AreaInput`, all seven exclusions, and the
arbitrary-center full-disk theorem.

**Next concrete step.** If CI reports a source error in the new module, fix the
first diagnostic (likely a library-name mismatch in the `2π/3` cosine sign
proof). If it is green, use `EdgeIncTo` at edge 0 as the template: prove the
corresponding positive-derivative prefix from a lower bound on `cosHiReal`,
then scale the coefficient checks per edge.

## 2026-10-30 (part 6) — repaired suffix cosine sign proof

**File / SHA256.** `SevenClassQ0Deg3EdgeSuffixNonpos.lean`
`3a2fde9dcd6bc6e72507dc54e19a6d4501ec60ae159bdb376be200ea9c82b6e8`.
`TARGETS.txt` SHA256 is unchanged at
`f17769f1b31723b4280df3dd8cff470db3a3060594eb45bae0da12595927fd54`.

**Fix.** In the `x > π` branch of `cos_le_neg_half_of_mem_suffix`, the prior
draft invoked `Real.cos_le_cos_of_nonneg_of_le_pi` with `x - π ≤ π/3` and
`0 ≤ x - π`: both are the wrong side of the needed comparison.  The revised
proof starts from `2π/3 ≤ x`, proves `π/3 ≤ x - π`, and applies the chord
monotonicity to `π/3 ≤ x - π ≤ π`, yielding `cos (x - π) ≥ 1/2` and hence
`cos x ≤ -1/2`.  No statement was weakened.

**Checks (scope).** `project_status.py --check`, `git diff --check`, and the
forbidden-token scan over the revised module pass.  A bounded
`mathlib-probe` `#check` attempt for the Mathlib lemma signature timed out at
45 s before producing output.  No Lean project build was run, so the module is
**drafted, CI pending**; none of its theorems are claimed kernel-green.

**Still unproved.** Kernel acceptance of this module and all prior lane-A
targets; the 42 `EdgeMonotone` facts; all 9 sectors; strict total;
`Degree3AreaCertificate`/`Q0Degree3AreaInput`; all seven exclusions; and the
arbitrary-center full-disk theorem.  The suffix argument currently pays only
decreasing suffixes for edges 9 and 10, conditional on CI.

**Next concrete step.** On the next CI run, read the first diagnostic in
`SevenClassQ0Deg3EdgeSuffixNonpos`; if green, prove `EdgeIncTo 0` from a
positive lower bound on `cosHiReal` on edge 0's increasing prefix, then use the
same coefficient/sign template across the remaining prefixes.

## 2026-10-30 (part 7) — corrected suffix cosine upper-bound direction

**File / SHA256.** `SevenClassQ0Deg3EdgeSuffixNonpos.lean`
`3b84d21d02401748a1f6690144ff34c0e5087edb586f788a0f25e9e14e44db8b`.
`TARGETS.txt` remains `f17769f1b31723b4280df3dd8cff470db3a3060594eb45bae0da12595927fd54`.

**Fix.** The `x > π` branch of `cos_le_neg_half_of_mem_suffix` previously
proved only `π/3 ≤ x - π`, but the desired `cos(x - π) ≥ 1/2` requires the
opposite endpoint: `x - π ≤ π/3`. It now derives `x - π ≤ π/3` from
`x ≤ piHi < 4π/3` and applies cosine antitonicity with `x - π` as the lower
endpoint. This repairs a genuine sign-direction error; it does not weaken the
statement.

**Checks (scope).** `git diff --check`, a forbidden-token scan of the module,
and `project_status.py --check` pass. These are static checks only. No Lean
build has run; the module remains **drafted, CI pending**. `LATEST.md` still
shows only the stale in-progress run `41008974701`.

## 2026-10-30 (part 8) — suffix witness domain hardened

**File / SHA256.** `SevenClassQ0Deg3EdgeSuffixNonpos.lean`
`1f3ac7d56a51da3b0e752c35adad0828d54b9d6563cc8abb14791a1ec675dbeb`.
`TARGETS.txt` remains `f17769f1b31723b4280df3dd8cff470db3a3060594eb45bae0da12595927fd54`.

Confirmed from the pinned Mathlib source that
`Real.cos_le_cos_of_nonneg_of_le_pi : 0 ≤ x → y ≤ π → x ≤ y → cos y ≤ cos x`
has the argument order used by the module. Replaced the witness-angle decimal
normalization with the exact order argument
`(2/3) * piLo < (2/3) * π = (2π)/3`, using only `piLo_lt_pi` and ring
normalization. The 90-second Mathlib probe did not finish importing, so the
source inspection is the evidence; no project build was attempted.

**Checks (scope).** `git diff --check`, forbidden-token scan, and
`project_status.py --check` pass. These are static checks only. The module is
still **drafted, CI pending**; neither suffix theorem is kernel-paid.

**Still unproved.** Kernel acceptance of this module and all prior lane-A
targets; the 42 `EdgeMonotone` facts; all 9 sectors; strict total;
`Degree3AreaCertificate`/`Q0Degree3AreaInput`; all seven exclusions; and the
arbitrary-center full-disk theorem.

**Next concrete step.** Read the first CI diagnostic for this module; if green,
prove `EdgeIncTo 0` from a positive lower bound on `cosHiReal` on edge 0's
increasing prefix, then use the same coefficient/sign template for the other
prefixes.
