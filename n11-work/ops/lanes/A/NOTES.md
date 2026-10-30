EXPERT (2026-10-30):
- C450 completion is genuinely CI-green; use it as the only paid Lane A result.
- Notes overstate endpoint status: at `6937fb90` EndpointChecks exits 1 and all downstream edge/sector targets are dependency-red.
- First repair EndpointChecks: replace vector tables with scalar defs/lemmas, use `rfl` or `simp only [nodeBinAt]; rfl`, and remove trailing tactics at lines 245/257.
- Then prove `sectorAt_zero_bin2_step_543 : sectorAt 0 544 ≤ sectorAt 0 543`; the current dec lemma allows `n = 543` but calls a lemma requiring `544 ≤ n`.
- After these, add one row-0 `SectorBinUnimodal` assembler; emit no more isolated bins until it is exit 0.
- `SectorValid`, strict total, `Q0Degree3AreaInput`, and all seven class exclusions remain unpaid.

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

## 2026-10-30 (session 66) -- row 0/bin 1 complete shape

**Did.** Added `SevenClassQ0Deg3SectorBin1.lean`.  Bins 0 and 1 have the same
exact node-table value (`239/1250`), so the already-green edge-0 cosine prefix
(monotone through node 543) pays all 255 increasing steps in bin 1.  The
audited witness 511 is the bin endpoint, making the decreasing half vacuous.
Also added the missing explicit `open SevenClassQ0Deg3Bins` needed by the new
index lemmas and by the prior bin-0 module.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBin1.lean`
`48c44cf84695f45b4d177d50dcaef672952716a2cbf239a677f9a1d084fc7452`.
`SevenClassQ0Deg3SectorBin0.lean`
`2f998326825b2865f41dabc1117814d9a3948e6b5a36a665361d7e258d39e406`.
`TARGETS.txt`
`2572b874db22cd3c75ed6b44470df441f37462448b6494593711f9f0e84dac2e`.

**Checks (scope).** `git diff --check` PASS and forbidden-token scan clean.
A Mathlib-probe attempt to kernel-check the two index lemmas was bounded at
240 s but timed out during the probe's Mathlib import; no Lean status follows
from it. No project oleans exist locally, so the new module is **CI pending**,
not kernel-green. The exact-rational 72-bin audit independently records node
511 as the row-0/bin-1 argmax.

**Still unproved / unpaid.** The other 70 row-bin shape obligations,
`SectorBinUnimodal`/`SectorValid`, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions.

**Next concrete step.** Let CI kernel-check the new target first. If green, do
row 0/bin 2: split at witness 543, using edge-0 increase through 543 and
decrease from 543; both node-543 and node-767 have `nodeBinAt 2`, so no node
jump interferes.

## 2026-10-30 (session 67) -- row 0/bin 2 drafted

**Did.** Added `SevenClassQ0Deg3SectorBin2.lean`.  It proves the increasing
half from bin start `512` through witness `543` using the same edge-0 cosine
prefix, with a fresh `nodeQ <= nodeQ 543` bound.  For the decreasing half it
checks the exact threshold at node `544`, proves the degree-28 cosine bracket
stays below row 0's threshold on `[node544, piHi]`, and packages the full
`Fin 8` row-bin obligation.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBin2.lean`
`4d0c9653985246a198fb57e343c48aa3aab7f4da35cb88d98faddb27a59e0cd4`.
`TARGETS.txt`
`65bc8dd9c22ed2dea4286a1fd8d2f66fc6dcad7b18b2ab8a9d1eec0d04f1962f`.

**Checks (scope).** `git diff --check` PASS; forbidden-token scan found only
the two `#print axioms` audits.  No local project build was run (no oleans; CI
is authoritative), so Lean status is **CI pending**, not kernel-green.

**Still unproved / unpaid.** The other 69 row-bin shape obligations,
`SectorBinUnimodal`/`SectorValid`, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions.

**Next concrete step.** Let CI check sessions 64--67.  If green, do row 0/bin
3: witness `768` is the bin endpoint, so its decreasing half is vacuous; the
cosine threshold drops at witness 543, requiring a new exact node-547/548
prefix check for the increasing half.

## 2026-10-30 (session 68) -- row 0/bin 3 drafted

**Did.** Added `SevenClassQ0Deg3SectorBin3.lean`. The witness `768` is the
bin's first grid point, so the increasing half is vacuous. For the full
decreasing half through bin endpoint `1023`, the module proves the exact
rational comparison `cosHiNLag (nodeQ 768) <= 2*mu(nextSite 0)/(19/50)^2`
and transfers the row-0 cosine upper bound across the whole bin. It packages
the complete `Fin 8` row-bin obligation.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBin3.lean`
`cdbad8ae8df6c4ffc91acb62ba2e5aaf009911d97de6f05f7fea72e51c6cb0f9`.
`TARGETS.txt`
`d74ddad1250502af8593c5e0bda74ee22f1adf88651101dea62de4b9f1b6907e`.

**Checks (scope).** `git diff --check` PASS; forbidden-token scan clean. No
local project oleans exist, so the module is **CI pending**, not kernel-green.
The exact-rational witness table independently records row-0/bin-3 argmax 768.

**Still unproved / unpaid.** The other 68 row-bin shape obligations,
`SectorBinUnimodal`/`SectorValid`, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions.

**Next concrete step.** After CI checks sessions 64--68, do row 0/bin 4:
witness `1024` is again the bin start, so only its decreasing half needs the
exact `cosHiNLag (nodeQ 1024) <= 2*mu/(19/50)^2` threshold and the fixed-bin
antitone transfer through `1279`.

## 2026-10-30 (session 69) -- row 0/bin 4 drafted

**Did.** Added `SevenClassQ0Deg3SectorBin4.lean`, proving the exact node-1024
cosine threshold, the row-0 antitone transfer through `1279`, and the complete
`Fin 8` row-bin obligation. The witness `1024` is the bin start, so the
increasing half is vacuous.

**Files / SHA256.** `SevenClassQ0Deg3SectorBin4.lean`
`63d8ff5cda0dbac04092e114530d7fa98e13d638803445ea93b83bddd0e58ba7`;
`TARGETS.txt` `93eb3306ea90ce8b614817a4ba9102bb454759b1c796b69fa5c3cae820c88fc0`.

**Checks (scope).** `git diff --check` PASS; forbidden-token scan clean. No
local project oleans/build; Lean status is **CI pending**, not kernel-green.

**Still unproved / unpaid.** The other 67 row-bin shape obligations,
`SectorBinUnimodal`/`SectorValid`, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions.

**Next concrete step.** After CI checks sessions 64--69, do row 0/bin 5
(witness `1280`, again the bin start): prove its exact node-1280 threshold and
antitone transfer through `1535`.
