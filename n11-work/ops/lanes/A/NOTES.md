# Lane A notes

## Ledger

- C450 Main/audit are CI-green (run `41123531381`); this is the only paid Lane A
  result. `Cos/Mono/Bins` are green, but `EndpointChecks` exits 1 and every
  edge/sector module downstream is dependency-red at `cc04268c`.
- All sector-reduction modules from session 55 onward are **CI pending** or
  dependency-blocked; none is kernel-green.
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

## 2026-10-30 (sessions 66--69, condensed)

Completed row-0 bin shape drafts 0--4 in `SectorBin0`--`SectorBin4`, adding
the needed `open SevenClassQ0Deg3Bins`.  None has a kernel-green claim.  The
key later correction was orientation of the decreasing cosine threshold and
separation of the sharp `543 -> 544` rational step from the derivative region.

## 2026-10-30 (session 70) -- bins 0--3 all rows, sharp boundary repair

**Did.** Found and corrected an orientation error in the untracked all-row
bin-2 draft: its decreasing lemmas proved `threshold <= cosHiReal` where the
calculus API requires `cosHiReal <= threshold`.  Also separated the sharp
step `543 -> 544` from the derivative region: the derivative is not negative
on all of `[node543,node544]`, so that one-grid-step decrease is proved by an
exact rational `norm_num` comparison.  The same repair was applied to the
tracked row-0 `SectorBin2` module.

Added the complete all-row bin-3 assembly.  Rows 0--1 peak at bin start
`768` (upper cosine crossing through `1023`); rows 2--8 peak at endpoint
`1023` (lower Taylor prefix from `768`).  Existing untracked all-row bins
0--1 and row-0 bins 5--7 were audited and are now listed for CI rather than
being silently omitted from `TARGETS.txt`.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBin2.lean`
`a50a0a163476ac78d7d8bb0ab8adee8e3c66128a059cf528b7b72039167f50ca`.
`SevenClassQ0Deg3SectorBins01AllRows.lean`
`ec327b5ed219ef406fe22408bdac55e96535914ed759648fd69b36661478170a`.
`SevenClassQ0Deg3SectorBins2AllRows.lean`
`828fb2b8cc881a92a04c894f79166ecd70a0e11d9f22e72c5f687cd386673179`.
`SevenClassQ0Deg3SectorBins3AllRows.lean`
`391050dae3a5649012c0de312ac24e7a34d9d5dc053de84461b0709d7775c2e4`.
`audit_q0_degree3_bins3_thresholds.py`
`a514d6327d5b2f0aaa8b37f25eb27709dc5d679eff4ff71534c72cc4016d1956`;
`q0-degree3-bins3-thresholds-audit.json`
`dc97660e53884ab9508315b3637207835a260e3016f6d3446f752426c0238aaa`.
`TARGETS.txt`
`e0134ad4ffbd91a3919dfd814747e76b4674e53a4507b1fcae9868830c6b1bc2`.

**Checks (scope).** `audit_q0_degree3_bins2_thresholds.py` PASS: 9/9 node-543
prefixes, 2/2 node-544 decreases, 7/7 node-767 endpoint increases.
`audit_q0_degree3_sector_bins.py` PASS: 72/72 exact-grid row-bin shapes,
including the discrete `543 -> 544` decrease.
`audit_q0_degree3_bins3_thresholds.py` PASS: 2/2 node-768 decreasing
crossings, 7/7 node-1023 increasing prefixes, 9/9 bin-3 argmax patterns.
`py_compile` and `git diff --check` PASS; forbidden-token scan is clean.  No
project oleans exist locally and no full Lean build was run, so all Lean
status is **CI pending**, not kernel-green.

**Still unproved / unpaid.** All-row bins 4--7 (36 obligations) remain,
as do the combined `SectorBinUnimodal`/`SectorValid` assembler, strict total
assembly, `Q0Degree3AreaInput`, and all seven class exclusions.  The existing
row-0 bins 5--7 and all-row bins 0--2 have no kernel-success claim yet.

**Next concrete step.** Let CI check sessions 64--70.  If green, prove bin 4
per row: rows 0--1 use the node-1024 upper crossing, while rows 2--8 have
row-dependent interior witnesses (`1173,1051,1076,1070,1076,1051,1173`) and
need separate exact lower/upper threshold checks on each side of the witness.

## 2026-10-30 (session 71) -- endpoint CI bottleneck repair

**Did.** Replaced the `endpointUBin` vector literal with an equation-compiled
scalar `Fin 8 → ℚ` definition, changed all eight endpoint scalar facts and all
eight `nodeBinAt` facts to kernel `rfl`, and made the two `< 5` finite proofs
explicit so no branch carries a stray `⊢` tactic. This targets the exact
`![...] 2` lookup and `No goals to be solved` failures reported by the expert
review; no mathematical table value changed.

**File / SHA256.** `SevenClassQ0Deg3EndpointChecks.lean`
`95bb9da1e3bd4f7524fbe929f81ef3dd9e7fa16376465b8a3f8704b4a738006e`.
`TARGETS.txt` is unchanged; `EndpointChecks` was already listed.

**Checks (scope).** `git diff --check` PASS; forbidden-token scan clean. A bare
Lean 4 `rfl` probe and the Mathlib probe were attempted, but both exceeded
their bounded timeouts during startup/import, so they give **no** verdict on
this file. No project oleans exist locally and no full build was run. Lean
status is **CI pending**, not kernel-green.

**Still unproved / unpaid.** EndpointChecks has no exit-0 claim yet; all
downstream edge/sector modules remain dependency-blocked. All-row bins 4--7
(36 obligations), the combined `SectorBinUnimodal`/`SectorValid` assembler,
strict total assembly, `Q0Degree3AreaInput`, and all seven exclusions remain.

**Next concrete step.** Let CI build `SevenClassQ0Deg3EndpointChecks`. If exit
0, immediately add the all-row bin-4 module: rows 0--1 decrease from 1024;
rows 2--8 increase to `w-1` then one exact step to `w`, and take one exact step
to `w+1` before the decreasing calculus tail, where `w` is the row-specific
witness. If red, read the exact failing line first; do not add bin 4.

## 2026-10-30 (session 72) -- all-row bin 4 drafted

**Did.** Added the complete all-row bin-4 module.  Rows 0--1 decrease from
`1024` using the exact node-1024 cosine threshold.  Rows 2--8 use witnesses
`1173,1051,1076,1070,1076,1051,1173`; the calculus prefix ends at `w - 1`,
the steps `w - 1 -> w -> w + 1` are exact rational checks, and the decreasing
calculus tail starts at `w + 1`.  The exact audit caught that rows 4--6 need
the two-step treatment; using `w` as the prefix endpoint would be false.
Also removed a duplicated `SectorBins3AllRows` entry from `TARGETS.txt`.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBins4AllRows.lean`
`a53fd01a1c903227481689bff4b15464c4a8fe97a9f67c3620f5156115e0bacf`.
`audit_q0_degree3_bins4_thresholds.py`
`5af9c69f71e271fdca67966686e850f1fb1986112b31e2ca00694afef9f9f58f`;
`q0-degree3-bins4-thresholds-audit.json`
`9b9d230a86b9df95b87d7aeaa6f5c74c3d31e7e51ef155843960b47edb8bf5c4`.
`TARGETS.txt`
`45504bcd6f5e9b90859c0419ad91efc6e682555367b6252bc29be7b53a92eb68`.

**Checks (scope).** `audit_q0_degree3_bins4_thresholds.py` PASS: 2/2
node-1024 crossings, 7/7 previous-node increasing prefixes, 7/7 next-node
decreasing tails, 7/7 `-2/3` cutoff comparisons, and 9/9 bin-4 argmax
patterns.  `py_compile`, `git diff --check`, and forbidden-token scan PASS.
No project oleans exist locally and no Lean build was run, so the new module
is **CI pending**, not kernel-green.

**Still unproved / unpaid.** `EndpointChecks` and all prior sector modules
remain CI pending.  All-row bins 5--7 (27 obligations), the combined
`SectorBinUnimodal`/`SectorValid` assembler, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions remain unpaid.

**Next concrete step.** Read CI's exact failing line if
`EndpointChecks` or this module is red.  If dependencies are green, draft
all-row bin 5; rows 0--1 have witness `1280`, rows 2--8 have witness `1280`
as well, but the prefix/tail threshold values still require an exact audit.

## 2026-10-30 (session 73) -- all-row bin 5 drafted

**Did.** Added the complete all-row bin-5 shape.  The exact 72-bin audit shows
that every row peaks at the first node `1280`, so all increasing halves are
vacuous.  A single all-row cosine-prefix threshold (`cosHiNLag` at node 1280)
then proves the decreasing half through `1535`.  This replaces the row-0-only
module as the route needed by the sector assembler.

**Files / SHA256.**
`SevenClassQ0Deg3SectorBins5AllRows.lean`
`7563e190db0370f90eee0d2083a019c180b3ae937f987b1cd4c48850dc1d202d`.
`audit_q0_degree3_bins5_thresholds.py`
`63d0118a5ff1faf4088aefc2888b6b4d27d81c0a0842dcf509b3b27e80a852d8`;
`q0-degree3-bins5-thresholds-audit.json`
`adf8089b23d2b56309741a45aa4306530e2308dc0737fa61d77fbbb4086a616e`.
`TARGETS.txt`
`90a22ddb5936d880188998bf8f3121da372136f06a49b46643bfe92ffd8d8138`.

**Checks (scope).** `audit_q0_degree3_bins5_thresholds.py` PASS: 9/9
node-1280 decreasing crossings, 9/9 `-2/3` cutoff comparisons, and 9/9
bin-5 argmax patterns.  `py_compile`, `git diff --check`, and forbidden-token
scan PASS.  No local project oleans exist and no Lean build was run, so the
module is **CI pending**, not kernel-green.

**Still unproved / unpaid.** `EndpointChecks` and all prior sector modules
remain CI pending.  All-row bins 6--7 (18 obligations), the combined
`SectorBinUnimodal`/`SectorValid` assembler, strict total assembly,
`Q0Degree3AreaInput`, and all seven exclusions remain unpaid.

**Next concrete step.** Audit all-row bin 6.  If (as expected from row 0) its
witness is `1536` in every row, reuse the same first-node decreasing template
and the `3*pi/4` tail bound, then list the new module in `TARGETS.txt`.
