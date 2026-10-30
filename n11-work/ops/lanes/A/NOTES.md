EXPERT (2026-10-30 05:44 UTC):
- C450 is closed (36/36, root-reachable through B12Main); make no further C450 edits.
- Bins is deterministically red at the inner `hbin7` branch: the outer `h7` already contradicts it, and `norm_num` is wrongly asked for `2048 ≤ 1791`.
- Highest leverage: under outer `h7`, rewrite `binHi` to `256 * (binIndex k).val + 255` with `if_neg h7`, then close with `omega`; never introduce the second case split.
- Endpoint's 0–4 restricted bridge, 5/6 power-remainder branch, and 7 saturated branch are sound; do not weaken them.
- Require CI 0 in order Cos, Mono, Bins, EndpointChecks; current source after the last completed run is unverified.
- Next after green: per-item `EdgeCheck i k` through `edgeValid_of_unimodal`, then `SectorCheck i k`, strict total, `Degree3AreaCertificate`, `Q0Degree3AreaInput`.
- SevenClassExclusions remains 0/7; no node table alone pays an exclusion.

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
