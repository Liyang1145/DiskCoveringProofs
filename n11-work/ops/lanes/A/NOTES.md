# Lane A notes

## Ledger

- C450 is closed at `495c970c`, CI-green, and transitively imported through
  `EnergyTerminalBatchB12Main`; stale `HARK-MISSING` comments are not a gap.
- Cos/Mono/Bins, EndpointChecks, C450 Main/audit, and all 42 edge-shape facts
  are CI-green at `1b2fa7a8` (run `41098508743`, job `124210423249`).
- The newer sector reduction modules are **CI pending**. Do not claim their
  kernel status until a run reports exit 0.
- `SectorValid`, strict `totalUpper < piLo`, `Q0Degree3AreaInput`, all seven
  exclusions, and the arbitrary-centre theorem remain unpaid.

## 2026-10-30 (sessions 24--54, condensed)

Repaired the C450 chain, Cos/Mono/Bins, EndpointChecks, 21 edge peaks, both
negative-edge suffixes, and all 42 edge-shape facts. Earlier CI reds isolated
`Nat.mod_lt` arguments, opaque Taylor terms, an incompatible composite
derivative, `decide` table facts, and `norm_num`/`omega` ordering. Exact audits
(not proofs) passed: 8/8 endpoint bins, 2048 cosine steps, 21 edge shapes, and
the `9 x 2049` sector grid.

## 2026-10-30 (sessions 55--63, condensed)

Added the sector peak, adjacent-step, calculus, bin-shape, witness, and witness
bounds modules:

- `SevenClassQ0Deg3SectorPeak.lean` reduces `SectorValid` to unimodality plus
  nine exact global peak checks.
- `SevenClassQ0Deg3SectorCalculus.lean` proves the fixed-node derivative is
  `(19/50)^2 * cosHiReal x / 2 - mu` and supplies monotone/antitone bridges.
- `SevenClassQ0Deg3SectorBinShape.lean` replaces the false global-step premise
  by 72 separate single-peaked row-bin obligations.
- `SevenClassQ0Deg3SectorBinWitness.lean` records the 72 audited argmaxes and
  proves all finite peak comparisons; the bounds module proves every witness
  lies in its stated bin.

Relevant hashes: peak `41c1b72d...543`, shape `90b7e764...7dd`, witness
`3fb1b952...195`, bounds `79eb307f...a4`. CI status: pending.

## 2026-10-30 (session 64) -- row 0/bin 0 increasing half

Added `SevenClassQ0Deg3SectorBin0.lean`, proving the exact table inequality
`2*mu(nextSite 0) <= edgeCoeff 0`, then using the already-proved edge-0 cosine
prefix with `sectorValue_le_of_cos_ge`. This covers all 255 increasing steps
through witness 255. Lean status at that point: CI pending.

## 2026-10-30 (session 65) -- row 0/bin 0 complete shape

**Did.** Extended `SevenClassQ0Deg3SectorBin0.lean`. The audited witness 255
is the last grid point of bin 0, so `sectorAt_zero_bin0_dec` is vacuous after
unfolding `binLast`/`binHi`; no false cosine-crossing claim was made.
`sectorAt_zero_bin0_unimodal` packages both ranges, all 255 increasing steps,
and the vacuous decreasing half as the complete `Fin 8` row-bin obligation.

**File / SHA256.** `SevenClassQ0Deg3SectorBin0.lean`
`cc6f5359b446a7309a7abeaa5d693740bda8cdaf1e523e12a5c698aa59c6bdea`.
`TARGETS.txt` already lists the module and was not reordered; its current hash
is `0979602de840a0d69cebf1f6757d59f4deca77b4e7e596ac8d8bd7b6f3db0682`.

**Checks (scope).** `git diff --check` PASS; forbidden-token scan found only
`#print axioms` audits; the vacuous-endpoint arithmetic matches the existing
exact-rational witness table. No project oleans exist locally and no full Lean
build was run. Lean status is **CI pending**, not kernel-green.

**Still unproved / unpaid.** The other 71 row-bin shape obligations,
`SectorBinUnimodal`/`SectorValid`, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions.

**Next concrete step.** Complete row 0/bin 1: prove its two boundary indices
have `nodeBinAt 1`, reuse the same edge-0 cosine bound (both are at most 543),
and note that witness 511 is again the bin endpoint so its decreasing half is
vacuous.
