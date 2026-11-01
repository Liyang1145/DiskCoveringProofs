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

## 2026-11-01 (session 138) -- C450 telescope independently re-audited

Re-read the entry/state guidance and ran `project_status.py --check` (PASS).
The restored `C450ChainCompletion` modules are present and CI-green; the root
still has both HARK markers and the supervisor-only import request remains.
Fresh local audits found no soundness shortcut at the empty tail: `source36`
is a member of `C450Source11Segment.remainingSegs`, hence paid by `h450`.

**Files / SHA256.** `C450ChainCompletion.lean` `d04b9dcf...eaf2a`;
`C450ChainCompletionMain.lean` `3f608861...539c`;
`C450ChainCompletionAudit.lean` `21abc908...3dfd`;
`C450ChainCompletionEndpoint/Tail/Mid1/Mid2/Mid3` hashes
`a9af5617...9f1`, `05d8bf4b...bc1`, `522f2c60...dce`,
`ebdcd8e9...766`, `f95882a7...229`.  Auditors:
`audit_c450_telescope_local.py` `2034e0ad...cbee`,
`verify_chain_completion.py` `e8496815...8bdb`.

**Checks (scope).** `audit_c450_telescope_local.py`: 25/25 transfers, 26/26
source/arithmetic rows, 26 source modules, terminal facts all true, zero
violations.  `verify_chain_completion.py`: all seven modules deterministic;
all five telescoping chunks exact; `Source31,26,21,16,11` types in order;
`h450` retains the `C450Source11` consumer type; no forbidden tokens.
`check_q0_degree3_edge_peak_unfold.py` PASS 21/21 and the sector analogue PASS
9/9; the import checker PASSes 48 references across 39 modules.  Emitter
replay reproduced identical bytes.  Fresh exact-rational replay also PASSed:
21/21 edges are single-peaked with witnesses, maxima and Lean coefficients in
agreement (`q0-degree3-edge-unimodal.json` `a35265eb...75bf`), and all 9x2049
sector values reproduce, including strict total slack `0.012092890370999008`
(`q0-degree3-sector-grid-audit.json` `f5a2b82d...f43`).  These are
source/arithmetic audits, not a new kernel verdict.

**Still unproved / unpaid.** The q0 peak owners and descendants remain CI
pending (no lane-A verdict after the lane-C OOM cancellations); sector
counterexample kernel acceptance, bin-wise sector shape, strict total,
`Q0Degree3AreaInput`, all seven exclusions, and the arbitrary-centre theorem
remain unpaid.  Root import of C450 is not yet done.

**Next concrete step.** On CI, run lane A before the lane-C residual census and
inspect `SevenClassQ0Deg3UpperReductionUnimodal` first; if green, inspect
`SectorPeak`, then the analytic step target.  Do not diagnose dependency-red
descendants.

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

## 2026-11-01 (sessions 145--146, condensed)
Split provenance checker PASS 9/9 against frozen `11f649b3`; textual only.
`audit_ci_lane_a_reachability.py` still reports `C B A` (`lane A position: 3`),
explaining why run `41293387736` died in B/C before any lane-A verdict.

## 2026-11-01 (session 147) -- direct step proof and strictness boundary
Probed the existing `sectorValue_row0_step_down` normalization in
`probe_q0_degree3_sector_step_normnum.lean`: bounded `lake env lean` timed out
after 180 s (exit 124, no diagnostic), so the emitted direct proof is not
CI-safe evidence.  I then tested reuse of
`sectorAt_bin3_dec_of_le_one 0 ... 1022`; it only yields a non-strict decrease,
which cannot refute the non-strict `SectorIncSteps` premise.  I reverted that
candidate proof rather than leave an invalid claim.

**Files / SHA256.** Emitter unchanged after revert
`360a51e0a6b815cb1a40b85c0b1f0507a91ee414928d7edfdec48dbcfde090c2`;
counterexample unchanged `644bb07a2a50597b8184a855277c1641e2ac21f9bb40f5fac738a85176b8bc9b`.
Re-ran the emitter (PASS), analytic audit (PASS, 78-digit positive margin),
`py_compile`, and `git diff --check`.

**Still unproved / unpaid.** No kernel verdict for the strict row-0 drop or
counterexample.  The direct 1237-digit rational normalization times out; the
bin-3 antitone theorem is insufficient without strictness.  All downstream
shape/bins/strict-total/exclusions/arbitrary-centre obligations remain unpaid.

**Next concrete step.** Add a strict-anti transfer theorem in
`SevenClassQ0Deg3SectorCalculus` using `strictAntiOn_of_deriv_neg`, prove the
derivative is negative on `(nodeQ 1022, nodeQ 1023)` from the exact
`cosHiNLag (nodeQ 1022) < 1/2` bound, then replace the counterexample's
normalization with that theorem.  Keep CI ordering blocker separate.
