EXPERT (2026-10-31):
- Direction is sound; C450 green modules are not class credit, and q0 remains 0/1 until strict-total CI is green.
- Run one serial chain: UpperReductionUnimodal, SectorPeak, edge suffixes/shape, sector calculus/bins, TableBounds, RelabelledTableCertificate, StrictTotal.
- Repair only the first owning error; dependency-red descendants are not diagnostics.
- After green prove `q0_degree3 : Q0RunExclusion 1` via `q0_degree3_of_areaInput q0Degree3AreaInput`; this is 1/7, not closure.
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions or raised heartbeats. Split EdgeShape if serial CI shows memory pressure.
 
# Lane A notes

CURRENT (session 131): the maintained sector-grid audit now uses Lean's
`nextSite` pairing.  No lane-A kernel verdict exists yet.

## Ledger

- CI-green paid Lane A targets: `C450ChainCompletionMain`,
  `C450ChainCompletionAudit`, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and
  `UpperTables`.
- At commit `7f7e6f3b`, the first lane reds were `UpperReductionUnimodal` and
  `SectorPeak`; every later edge/sector/table target was dependency-red.
- `SectorValid`, strict `totalUpper < piLo`, `Q0Degree3AreaInput`, all seven
  exclusions, and the arbitrary-centre theorem remain unpaid.

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).

## 2026-10-31 (sessions 115--131, condensed)

Replayed edge derivative/unimodal and sector-grid audits: 21 edge peaks, 21
discrete peaks, 18,441 sector points, 72/72 bin witnesses, 18,369 within-bin
steps, 63/63 jumps, and strict-total slack `0.012092890370999008`. Repaired the
edge 1/8 endpoint comparisons, frozen-`piHi` maxima, `mu (nextSite i)` pairing,
and emitter witness mismatch. These are source/arithmetic checks only;
`degree_three_table_graph` still has a `sorryAx` dependency and no kernel credit.

## 2026-10-31 (session 132, condensed) -- CI owner repair

Run `41237352391` had C450/Main/Audit, Cos, Mono, Bins, EndpointChecks and
UpperTables green; both peak owners were red. The independent errors were a
coefficient-sum mismatch in `edgeValid_of_unimodal` and unreduced vector
projections in peak proofs. Added the exact edge equality and scalar
projections for 21 `edgeMaxAt` / 9 `sectorMax`; textual gates were 21/21 and
9/9. This repair was CI pending, not proof credit; all peaks and descendants
remained unpaid.

## 2026-11-01 (session 133) -- false global sector-step premise quantified

Ran the exact rational sector-step audit on the current tree.  It confirms that
the global adjacent-step premise `SectorAdjacentUnimodal` in
`SevenClassQ0Deg3SectorShape` is false for every one of the nine rows; the
correct paid route remains the eight-bin reduction in `SectorBinShape` /
`SectorAssembler`.  I found no source consumer of the false theorem outside its
own defining module.

Extended `audit_q0_degree3_sector_steps.py` to record each row's strongest
exact failure; row 0 is index 1022, drop `7.421500301204...e-5`. Files:
`audit_q0_degree3_sector_steps.py` `47293a57...bac266`;
`q0-degree3-sector-steps-audit.json` `3b6d4c38...0cd3c7b7e`.

**Checks (scope).** Exact-rational replay PASS: all nine maxima reproduce and
all nine rows refute both global adjacent-step directions; strongest row-0
increasing drop `7.421500301204045e-5`.  `py_compile` and `git diff --check`
PASS.  This is arithmetic/source evidence, not kernel or proof credit.

**Still unproved / unpaid.** Kernel acceptance of the peaks and the entire
bin-wise sector chain; sector/edge shape kernel checks; table/strict-total;
`Q0Degree3AreaInput`; seven exclusions; arbitrary-centre theorem.  The false
`SectorAdjacentUnimodal` interface must not be used as a premise.

**Next concrete step.** Add `SevenClassQ0Deg3SectorStepCounterexample` with a
kernel proof of `¬ SectorAdjacentUnimodal` using index 1022 (row 0), after the
peak owners are green; add it to lane-A `TARGETS.txt` only when written.

## 2026-11-01 (sessions 134--137, condensed) -- sector-step counterexample, CI blocked

Emitted `SevenClassQ0Deg3SectorStepCounterexample` (`644bb07a...bc9b`) from
the row-0 1022 -> 1023 decrease; the emitter is `360a51e0...090c2`.  The exact
drop has a 1237-digit numerator.  A coarse analytic audit
(`9dfccf6e...3f36f`, JSON `1c512402...56faf`) proves the endpoint separation
using the degree-29 remainder, but direct giant-literal `decide +kernel`
probes timed out and are not evidence.  CI runs `41266567914` and
`41271050741` never reached lane A: lane C's residual census was killed
with exit 143, so both peaks and the counterexample remain CI pending.  The
false `SectorAdjacentUnimodal` must remain unused.

## 2026-11-01 (session 138, condensed) -- C450 telescope re-audited

`project_status.py --check` PASS.  C450/Main/Audit and all five telescoping
chunks are CI-green; root still has both HARK markers, so the supervisor-only
ROOT-IMPORT REQUEST remains.  Fresh local audit: 25/25 transfers, 26/26
source/arithmetic rows, `Source31,26,21,16,11` in order, no empty-tail
shortcut (`source36` is in `Source11.remainingSegs`).  Exact edge/sector
replay PASSed (21 edges; 9x2049 sectors; strict slack `0.012092890370999008`).
These were source/arithmetic checks, not kernel credit.

## 2026-11-01 (session 139, condensed) -- direct step evaluation ruled out

Job `124743726683` (run `41271050741`) died at lane C with exit 143 after
memory fell to 1935 MB, before lane A.  A dependency-free Mathlib probe
`probe_q0_degree3_sector_step_normnum.lean` (`60292677...dfb6a`) timed out at
120 s, so direct `norm_num` over the 1237-digit step comparison is not viable.
The exact analytic audit still gives a separation margin; the intended route
is a `sinHiNLag`-step lemma.  No proof credit followed from the probe.

## 2026-11-01 (session 140, condensed) -- peak projections made definitional

Replaced 30 giant-rational `decide +kernel` max projections by `rfl`; the
pre-split source hash was `69e6eabf59a15a034a8c3bb8b53b665a85f785a7191227960b8d2533ab92c367`.
Exact-literal and unfold gates passed. No kernel verdict followed.

## 2026-11-01 (session 141) -- resumed current peak artifacts

Re-ran the entry checks and the three fast peak-source gates.  `project_status.py
--check` PASSed its handoff-index scope.  The projection, edge-unfold and
sector-unfold checkers all PASS (21/21 edge and 9/9 sector).  Current peak hashes
remain edge `69e6eabf...c367`, sector `e124cce5...bea`, counterexample
`644bb07a...bc9b`; no CI run has produced a lane-A kernel verdict since run
`41289029262`.

**Still unpaid.** Kernel acceptance of both peak owners and the step
counterexample, all downstream sector-bin/shape/calculus targets, strict total,
`Q0Degree3AreaInput`, seven exclusions, and the arbitrary-centre theorem.

**Next concrete step.** Split the edge peak proofs into a definition-only base
plus three 7-row proof modules, then make the existing module a thin assembler;
this preserves theorem names while bounding each target's elaboration memory.

## 2026-11-01 (session 143) -- edge peaks split to one row per module

Run `41293387736` (job `124809123036`) never reached lane A: lane B's
`EnergyTerminalBatchB13RefineSixteenResidualCensus` exhausted memory at 388 MB
available, and the runner shut down while building lane B's Main target. I
applied the planned lane-local mitigation: each of the 21 proof bodies is now
alone in `SevenClassQ0Deg3UpperReductionUnimodalPeak00..20.lean`; the three
7-row modules are import-only group assemblers; the public assembler is
unchanged. All 21 row files have sorted `sha256sum` manifest hash
`98ad699a1d1a17bf4ba4900b9f830dfad3685aef4d21afe7594540618819114c`.

**Files / SHA256.** Groups `Peaks0To6`
`fad63922c0d79eccf2c6a02e1587d52cb5a5c8434d8fb7c6f4292b1c0048a7d8`,
`Peaks7To13` `18ceda639e855f2663bc491e78c5b27ac6dce471a2d4d8a9056a2068cb1e8918`,
`Peaks14To20` `708aeb8583858ca7bb669b4abe30789c604eebbed9db706cb084d0f674298267`;
assembler `620f7830a09b2bbad5f9489f5cb7a442cbb72867dd8ae741221e567d2a656af0`;
emitter `90118205ef347aa15f82e42df6256271337ce3c2dfdfad590e366a771b9954be`.
All 21 row targets are listed explicitly in `TARGETS.txt`.

**Checks (scope).** `project_status.py --check` PASS (handoff index only).
Split provenance PASS: all 21 bodies byte-identical to frozen `a0f0f971` and
declared once. Edge-unfold PASS 21/21; max-projection PASS 21 edge + 9 sector;
import closure PASS 94 refs/64 modules; emitter byte-deterministic; `py_compile`
and `git diff --check` PASS. These are textual/generator checks, not kernel
evidence; no local project olean exists.

**Still unproved / unpaid.** All 21 row modules, three groups, assembler and the
sector-step owner are CI pending. Kernel acceptance of the sector peak, all
downstream bin/shape/calculus targets, strict total, `Q0Degree3AreaInput`, seven
exclusions, and the arbitrary-centre theorem remain unpaid. Root import of C450
stays supervisor-only.

**Next concrete step.** CI lane A must run before lanes B/C; build Base, rows
00..20, groups, assembler in order and inspect the first red row. Lane B's
runner-killing census must be moved after lane A by the supervisor.

## 2026-11-01 (session 144) -- sector peaks split to one row per module

Converted `SevenClassQ0Deg3SectorPeak.lean` into a definition-only base,
nine one-row proof modules, and a thin assembler preserving
`sectorPeakValid_0..8`, `sectorPeakValid_all`, and `sectorValid_of_shape`.
The emitter now writes all eleven files; `TARGETS.txt` lists base and rows
before the assembler. Base `0a67ec6d...8de9`; row-manifest hash
`535dea7a...a18b`; assembler `b9285a0b...f9d0`; emitter `24c09e79...049f`;
unfold checker `c782e68f...57fa`; projection checker `ca94478e...8aed`.

**Checks (scope).** Projection PASS: 21 edge + 9 sector max rewrites are exact
`rfl`; sector-unfold PASS 9/9; explicit-import closure PASS, 113 refs/74
modules; emitter byte-deterministic over two runs; `py_compile` and
`git diff --check` PASS. These are textual/generator checks, not kernel proof.

**Still unproved / unpaid.** All eleven split sector modules are CI pending.
Peak/sector kernel acceptance, analytic shape, bins, strict total,
`Q0Degree3AreaInput`, seven exclusions, and arbitrary-centre theorem remain
unpaid. Root import of C450 stays supervisor-only.

**Next concrete step.** CI lane A builds Base then rows 00..08 then assembler;
inspect the first red row and split no further unless a one-row target exits.

## 2026-11-01 (session 148) -- strict step from analytic Lipschitz bound

Replaced the counterexample's direct 1237-digit `norm_num` with a strict
bin-3 theorem.  `SectorCalculus.sinHiNLag_sub_le_of_grid` proves the upper
sine bracket is 1-Lipschitz on the grid range by showing
`sinHiReal x - x` is antitone (its derivative is `cosHiReal x - 1`, and
`cosHiReal x ≤ 1`).  `SectorBin3.sectorValue_zero_strict_dec_of_bin3` then
combines that bound with row 0's exact coefficient
`(19/50)^2/2 - mu (nextSite 0) < 0`.  The counterexample now applies the
1022 < 1023 instance directly.

**Files / SHA256.** `SectorCalculus`
`14894ced8af03b20f23367baf95cebebee3d905b391be86be45371e1541778e9`;
`SectorBin3` `6dc01fa698f4da55b014eaea12fb3a1157de3377fa5bdfad10041e6e6110d5c4`;
counterexample `f7ec67ed19953b15e8b3f8f25156f14ffe391df531acbea3c825386317132f68`;
emitter `03a8a961fb294290dc72b46f78c9639e1d88bf32c0566bb1ef99fe4ff7e73ba0`.
`TARGETS.txt` now lists the counterexample immediately after bin 3.

**Checks (scope).** Re-ran the exact-rational analytic audit: positive
separation margin, PASS (`q0-degree3-sector-step-analytic-audit.json`
`1c512402ae39be280fc68593385c11a0cda787f4026f630960858ea5b4a56faf`).
Sector/edge split provenance PASS, import closure PASS (114 references/74
modules), emitter deterministic, `py_compile`, forbidden-token scan and
`git diff --check` PASS.  These are source/arithmetic checks only; no local
project olean or kernel verdict exists.

**Still unproved / unpaid.** The new Lipschitz lemma, strict bin-3 theorem and
counterexample are CI pending.  Peak owners, the remaining bin-wise sector
chain, strict total, `Q0Degree3AreaInput`, seven exclusions and the
arbitrary-centre theorem remain unpaid.

**Next concrete step.** CI must build `SectorCalculus`, then bin 3, then the
counterexample in that dependency order.  Inspect the first owned kernel error;
do not diagnose dependency-red bin 4--7 descendants.

## 2026-11-01 (session 149) -- false strict coefficient caught and repaired

The preceding strict bin-3 draft was invalid: it used the global 1-Lipschitz
sine bound and asserted `(19/50)^2/2 - mu < 0`, but exact arithmetic gives a
positive value (about `0.02365`).  Replaced that route with a local cosine
bound.  `SectorCalculus.sinHiNLag_sub_le_of_cos_le` turns a pointwise
`cosHiReal x <= c` bound into `sinHiNLag b - sinHiNLag a <= c * (b-a)`.
`SectorBin3.cosHiReal_le_one_half_of_nodeQ_768_le` proves `c = 1/2` on the
whole bin (Taylor tail above `pi/2`, monotonicity below); the resulting
coefficient `(19/50)^2/4 - mu` is exactly negative.

**Files / SHA256.** `SectorCalculus` `98ce6dd8...6ee6`; `SectorBin3`
`65ea1f17...472b`; counterexample unchanged `f7ec67ed...2f68`; audit script
`b6e951a8...6363`.  Refreshed evidence JSON
`q0-degree3-sector-step-analytic-audit.json`
`5f8f5aaf48ebd91ce26cebb927ad258ee58bcb4aa29cd27d41d710b45ef86bdb`.

**Checks (scope).** Exact-rational audit PASS: step 1022 -> 1023 drops, old
margin positive, and new coefficient `A^2/4 - mu < 0`; `py_compile` and
`git diff --check` PASS.  No local Lean kernel check was run.

**Still unproved / unpaid.** The new cosine-half and Lipschitz lemmas, strict
bin-3 theorem, counterexample, peaks, remaining bins, strict total,
`Q0Degree3AreaInput`, seven exclusions, and arbitrary-centre theorem are all
CI pending/unpaid.

**Next concrete step.** CI lane A must build `SectorCalculus`, `SectorBin3`,
then `SectorStepCounterexample`; inspect the first owned kernel error.  Lane A
remains unreachable while global lane order is `C B A`.
