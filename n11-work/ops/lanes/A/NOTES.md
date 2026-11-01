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

## 2026-11-01 (session 133, condensed) -- false global sector-step premise

Exact arithmetic refutes `SectorAdjacentUnimodal` on all nine rows; row 0
fails at 1022 -> 1023 by `7.421500301204045e-5`. The bin-wise reduction is the
valid route. Audit script `47293a57...bac266`, JSON `3b6d4c38...0cd3c7b7e`.
Checks were exact-rational/source only.

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

## 2026-11-01 (session 148, condensed) -- analytic strict-step draft

Drafted the 1-Lipschitz/SectorBin3 strict-step route.  Exact audit and source
checks passed, but session 149 found its coefficient premise false and replaced
it; do not use the session-148 coefficient.  Counterexample remains CI pending.

## 2026-11-01 (session 149, condensed) -- strict bin-3 repair

Replaced a false global-Lipschitz coefficient with the local bound
`cosHiReal x <= 1/2` on bin 3. `sinHiNLag_sub_le_of_cos_le` then makes the
strict coefficient `(19/50)^2/4 - mu(nextSite 0)` exactly negative. Files:
`SectorCalculus` `98ce6dd8...6ee6`, `SectorBin3` `65ea1f17...472b`, audit
script `b6e951a8...6363`, evidence `5f8f5aaf...86bdb`. Arithmetic/source only;
all Lean targets remain CI pending.

## 2026-11-01 (session 150) -- first seven-class consumer

Added `SevenClassQ0Deg3Q0Exclusion` as the thin, exact consequence
`q0_degree3_of_areaInput SevenClassQ0Deg3StrictTotal.q0Degree3AreaInput`; it
creates no new premise.  Added it after `StrictTotal` in `TARGETS.txt`.

**Files / SHA256.** `SevenClassQ0Deg3Q0Exclusion.lean`
`2a0fa29804461a8e3965b37f370b6c0ed81ee730602e28fdd0209d66767e8875`;
`TARGETS.txt` `5a0f9daab67054c83fee14099afdf188ab5a5442bb516dd586f30a7e0085aee0`.

**Checks (scope).** Source gate PASS: exact import, one ordered target after
`StrictTotal`, forbidden-token scan, `py_compile`, and `git diff --check`.
Exact-rational sector-step replay PASS (positive separation; refreshed JSON
`5f8f5aaf...86bdb`).  These are source/arithmetic checks only; no Lean kernel
check ran.  Current CI run
`41309394801` (sha `35a51aef`) never reached lane A: lane C's
`EnergyTerminalBatchB13RefineSixteenResidualCensus` drove available memory from
11.9 GB to 1.7 GB in 80 s and the runner exited 143.  The previous run
`41301935749` was killed at the same target.  Thus no current lane-A source has
a kernel verdict.

**Still unproved / unpaid.** `StrictTotal.q0Degree3AreaInput` is CI pending, so
the new `q0_degree3` is CI pending rather than paid.  All other six exclusions,
remaining sector/edge binary targets, and arbitrary-centre theorem stay unpaid.

**Next concrete step.** Supervisor must isolate lane A from the lane-C census
(e.g. a separate workflow job or A-first dispatch); then CI should build
`StrictTotal`, `Q0Exclusion`, and audit the new axiom report.

## 2026-11-01 (sessions 151--153) -- bin-3 half bound repaired, kernel pending

Found a source proof defect in `cosHiReal_le_one_half_of_pi_div_two_le`:
`cos_bound_abs` and the definition of `cosHiReal` each contribute the tail
term, so `4^28/28! <= 1/2` only yielded `cosHiReal <= 1`.  Tightened it to
`4^28/28! <= 1/4`; `cos <= 0` plus the two error contributions then yield
`cosHiReal <= 1/2`.  Session 153 replayed the exact-rational audit after the
repair: all four scalar inequalities PASS, including the quarter bound.

**Files / SHA256.** `SevenClassQ0Deg3SectorBin3.lean`
`1f082d0ad68579543fb45910ed703292d447b015f9a473a895767b3500536673`;
`audit_q0_degree3_bin3_local_cos.py`
`dee794233502a3b94c6d81aa7616456efbf54571bf49b30b3398b37a67198124`;
`q0-degree3-bin3-local-cos-audit.json`
`5e2a34af5145e8b516cef7eb94cc91fefb7697dd05f45b7415f616bffac4dcc9`.

**Checks (scope).** Session 153 reran the exact audit PASS and confirmed source
and evidence hashes unchanged.  Two bounded standalone Mathlib probes (full
`Mathlib`, then minimal Real/Linarith/NormNum imports) timed out at 120 s and
100 s while importing, so no local Lean kernel check exists; `SectorBin3`
remains CI pending.  These checks do not cover the theorem's elaboration.

**Still unproved / unpaid.** `SectorBin3` repair, strict total,
`Q0Degree3AreaInput`, `Q0Exclusion`, the other six exclusions, and the
arbitrary-centre theorem are not paid. `TARGETS.txt` is unchanged.

**Next concrete step.** A-first CI must build `SectorCalculus`, the repaired
`SectorBin3`, and then `SectorStepCounterexample`; inspect the first red owner
before changing downstream modules.
