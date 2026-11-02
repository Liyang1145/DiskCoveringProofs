# Lane A notes

CURRENT (session 184): `Q0Degree5ClosureExtension` instantiates the exact
source box coordinates and proves nonnegativity plus the full `[0, pi]` ranges
for both base angles and the sector width.  Concrete factor maxima and strict
source total remain missing.  Module **CI pending**; no exclusion is claimed.

## Ledger

- CI-green paid Lane A targets: `C450ChainCompletionMain`,
  `C450ChainCompletionAudit`, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and
  `UpperTables`.
- Repair only the first owning error; dependency-red descendants are not
  diagnostics.  A green q0 chain would prove `q0_degree3 : Q0RunExclusion 1`
  (1/7).
- Keep explicit `edgeUpper`/named-constant unfolding; no decimal substitutions
  or raised heartbeats.
- `SectorValid`, strict `totalUpper < piLo`, `Q0Degree3AreaInput`, all seven
  exclusions, and the arbitrary-centre theorem remain unpaid.

ROOT-IMPORT REQUEST: import the CI-green `C450ChainCompletion` and
`C450ChainCompletionMain` in the stage-1 root (supervisor-only edit).

## Condensed history

- Sessions 115--153 exactly audited 21 edge peaks, 21 discrete peaks, 18,441
  sector points, 72/72 bins, 18,369 within-bin steps, 63/63 jumps, and bin-3
  (256 nodes / 32,640 pairs).  Global sector unimodality was refuted; the valid
  route is bin-wise.  These are source/arithmetic checks, not kernel credit.
- Sessions 142--153 split 21 edge and 9 sector peaks and repaired the bin-3
  half bound.  All split/calculus/bin/table modules remain CI pending.
- C450/Main/Audit, `Cos`, `Mono`, `Bins`, `EndpointChecks`, and `UpperTables`
  are CI-green.  Root still carries both HARK markers.
- Sessions 158--162 found and repaired earlier base errors, then identified CI
  lane routing as the reachability blocker.  Session 159 introduced
  `SevenClassQ0Deg3Repaired.lean`, a generated copy of frozen SHA
  `48d41f5d3a71c41adc3ff0af26f86740b2f4ed82383a037d182aac0f16075b61`
  adding only the missing census import and ear-count open.
- Sessions 165--166 made the strict-total division bounds goal-shaped with
  `div_le_div_of_nonneg_right`; exact ledger checks passed, but no Lean verdict
  was obtained.
- Session 167 read the live log of run `41378003343`.  First owners were the
  repaired-copy import placement, nine sector peak rational comparisons, and
  the 21 edge coefficient equalities.  The log's peak goal reduces to a huge
  fraction-to-fraction inequality; the edge goal reduces to a literal rational
  versus a two-term `Finset.sum`.  Fixes: move provenance below imports and add
  terminal `decide +kernel` to those bounded closed rational goals.  No frozen
  module, arithmetic table, or theorem statement changed.

## 2026-11-02 (session 168, condensed) -- repaired q0(3) tree audited

Run `41378003343`'s first residual goals were exact closed rational shapes, so
terminal kernel suffixes were targeting the right comparisons.  Deterministic
regeneration, 9/9 sector split-preservation, exact recomputation of all nine
maxima, banned-token/import/TARGETS audits, and `git diff --check` passed.  No
local kernel verdict was obtained.  Any failed CI suffix must be repaired in
that single closed goal, not by changing arithmetic tables.


## 2026-11-02 (sessions 169--174, condensed) -- CI boundary and repair audits

No n=11 Lean job has existed for the repaired tree: runs `41380560959` and
`41399703011` are pending with no jobs; older runs predate the repairs.  Six
sessions therefore produced source/arithmetic evidence only, never a kernel
verdict.  Useful results: the q0 import-closure checker was corrected (skip a
file's own namespaces) and `SevenClassQ0Deg3Q0Exclusion` was found not to import
`SevenClassQ0Deg3`; adding that direct import moved the closure audit to PASS
(115 references across 76 q0 modules).  `audit_q0_degree3_kernel_cost.py`
records literal sizes sent to terminal `decide +kernel`: sector peaks 00--08
have 2071--2099-bit largest literals, the edge module 141-bit.  A core-only
363-bit Rat probe timed out at 50 s and is inconclusive, not a rejection.
Strict-ledger exact arithmetic PASS with total `3.135646999268476` and slack
`0.005945654321317` (Python rationals, not Lean).  Other rerun preflights
(sector split 9/9, edge split 21/21, q0 repair, unfold/max projection) PASS in
their source-check scopes.  All q0 Lean modules remain CI pending; the other
six exclusions, `Q0Degree3AreaInput`, strict total, and the arbitrary-centre
theorem remain unpaid.

## 2026-11-02 (session 175) -- q0(5,8) graph matched; source coefficients not exact

Extended the seven-class graph audit from the q0(4,9) pilot to the q0(5,8)
closure case.  New script `audit_q0_degree5_graph.py` verifies that
`q0_closure_dual_0_3.json` declares `start=0, span=3`, 11 faces and 21 edges and
that its labelled face set and edge set equal `ActualOrderedMetricGraphs.q0Faces 3`
(reconstructed independently from `q0Fan`/`centralFace`).  It also checks the
certificate header (`strict=true`, same span), 121 coefficients, 121 `z` slots,
and the 11+9+9 factor-label order.  Result: **PASS_SOURCE_GRAPH_AND_LAYOUT_ONLY**,
`q0-degree5-graph-match.json`, sha256
`8daf9efdd67f7349de92533ceb750f633cebd16f006b1dcb88566dae99285c00`;
script sha256 `9dca117fd1904fbdaf1656f343a8757dde0fb59cdfa991119a544bd44db32bdb`.

Material finding: unlike the q0(4,9) pilot, the q0(5,8) certificate stores all
121 coefficients as **decimal strings** and `z` as binary floats, not exact
rational pairs.  This file therefore cannot be a Lean coefficient source; an
exact-rational certificate must be regenerated by the source emitter before a
`Q0Degree5FiniteTable` can be written.  No factor bound, balance, or exclusion
is proved by this audit.

**Checks run (scope).** The new graph/layout audit above; `python
tools/project_status.py --check` PASS (handoff index only).  No Lean build; CI
still shows run `41399703011` pending with no job, so every q0 module and the
new audit's (nonexistent) kernel claims remain CI pending/unpaid.

**Files.** Added `audit_q0_degree5_graph.py` and `q0-degree5-graph-match.json`.
No Lean, TARGETS, frozen, root, or toolchain file changed.

**Still unproved / unpaid.** q0(4,9)/q0(5,8)/q1(3,9)/q1(4,8)/q1(5,7)/q1(6,6)
tables, all exact factor bounds, the seven exclusions, energy, and the
arbitrary-centre theorem.  q0(5,8) additionally lacks exact rational
coefficients.

**Next concrete step.** Regenerate q0(5,8) coefficients from the committed
source emitter in exact `Fraction` form and extend the audit to compare the
emitter's graph/field order; only then emit `Q0Degree5FiniteTable.lean`.

## 2026-11-02 (sessions 176--178, condensed) -- q0(5,8) source reconstruction

`reconstruct_q0_degree5_exact.py` parsed the stored decimal literals as
`Fraction`, verified the 121-slot layout and certificate copy/order, and wrote
`q0-degree5-exact-source.json` (SHA `900d2186...f41d`).  The emitter
`emit_q0_degree5_source_data.py` then wrote `Q0Degree5SourceData.lean` with all
121 exact rationals and graph identities to `q0Faces 3`/`q0Edges 3`; TARGETS
registers it.  A stripped-import syntax probe timed out, so its Lean status is
CI pending, not green.  `map_q0_degree5_canonical_data.py` mapped the direct
`CanonicalCoeffQ` groups but left the nine closure slots open.

## 2026-11-02 (session 179) -- q0(5,8) closure interface obstruction identified

Added `audit_q0_degree5_closure_interface.py`.  It checks all 121 exact source
coefficients, the recorded source-emitter SHA, the emitter's exact closure
term/constant formulas, 9/9 strictly positive closure multipliers, zero `eta`
and zero `width`, and compares the source and canonical pi-coefficients exactly.
The source coefficient is `station + kap - 2*lambda - sum(closure)`; the current
canonical formula is `station + kap - 2*width - 2*eta`.  With the existing map
the exact `canonical_minus_source` is
`195718067274616349/100000000000000000`.

The mismatch is stronger than a scalar offset: closure enters each sector as
`closure[i-1]*(left+w/2)+closure[i]*(right+w/2)` and each switch as
`2*b*closure[j]`.  `CanonicalCoeffQ` has no `Fin 9` closure field, and scalar
`eta` cannot repair those sector/switch-dependent objective terms.  Therefore
emitting `Q0FiniteTable 3` through the current interface would be unsound.

**Files/shas.** audit script
`1d9d257f9fafc3fb58637583521feba1b74f1e5dc7d1650951823789e8ce289a`;
report `q0-degree5-closure-interface-audit.json`
`7c21573011960c0f7fee9a06c779619420ee26a9c318b2ef6bb8550510e7f8c2`.

**Checks (scope).** `py_compile` PASS; exact audit PASS; `git diff --check`
PASS.  This is source/interface arithmetic only, with no Lean build and no
kernel claim.  All q0(5,8) bounds and strict total remain unpaid.

**Next concrete step.** Add a new closure-extended certificate module carrying
`closure : Fin 9 → ℚ`, closure nonnegativity, the `-π*sum(closure)` constant,
and closure-augmented sector/switch objectives with sound consumers; then
instantiate it from the hash-bound source data.  Do not edit frozen modules.

## 2026-11-02 (session 181) -- closure nonnegativity and sound bound lifting

Added actual base angles, their nonnegativity, nonnegative switch/sector closure
terms, and lifting lemmas from augmented to base objectives.  No bounds instance
was asserted.  Module `32dfdde8...`, audit `ec8fd42b...`, report `2e0fbc14...`.
Checks: `py_compile`, exact audit, and `git diff --check` PASS; Lean **CI
pending**, not paid.  Unproved then: all closure-aware bounds, strict total,
q0(5,8) exclusion, six classes, energy, and arbitrary-centre theorem.

## 2026-11-02 (session 182) -- closure-aware bounds recover the canonical interface

Added `ClosureSectorCoordinates` for the source's box-dependent base angles and
width, `ClosureFactorBounds` with exact nine-multiplier switch/sector additions,
and `ClosureCertificate`.  Proved the coordinate-nonnegativity lifting to
`CanonicalFactorBounds`, `ClosureCertificate.toCanonical`, and `total_lt_pi`;
also defined `closureTotalUpperQ`/`closureTotalUpper`, proved
`constantTerm_nonpositive`.  No concrete factor bound or certificate instance
is asserted.  Initial fixed-realized-tie version was corrected before handoff:
source sector closure terms vary over the generic box.

**Files/shas.** `Q0Degree5ClosureExtension.lean`
`163e75dd2a219a32ad578f50f725351fcf934561a4d8275a0c92a23264d5c8e3`;
audit `audit_q0_degree5_closure_extension.py`
`c0360b6f41f4609c4334acdce28d15d27ca0dcdf5114f351f87dd4bf022bb52c`;
report `q0-degree5-closure-extension-audit.json`
`3204a7ea6a9bdf0d3f6d1e085336067c66e5b9077a307f8011be27531204b41c`.

**Checks (scope).** `py_compile` PASS; exact source/interface audit PASS
(including the four new declarations); `git diff --check` PASS.  No local Lean
build and no CI verdict, so the new Lean declarations are **CI pending**, not
paid.  Still unproved: 11 face bounds, 9 switch bounds, 9 closure-aware sector
bounds, concrete strict-source total, q0(5,8) exclusion, six other classes,
energy, and the arbitrary-centre theorem.

**Next concrete step.** Define the exact box-coordinate source functions for
`ClosureSectorCoordinates` (or prove the realized-angle bridge), then emit exact
finite face/switch/sector maxima, recheck the strict total, and only then
instantiate `ClosureCertificate`.

## 2026-11-02 (session 183) -- exact source box coordinates instantiated

Transcribed the normalized coordinate formulas from the hash-bound source
emitter `q0_closure_dual.py`: chord
`sqrt(u^2+v^2-2uv cos a)`, width
`2 asin((19/50) chord/2)`, and the two `atan2` base angles as `Complex.arg`.
Added `sourceSectorChordLength`, `sourceSectorWidth`,
`sourceLeftBaseAngle`, `sourceRightBaseAngle`, `sourceSectorCoordinates`, and
proved all three box-domain nonnegativity fields required by
`ClosureFactorBounds`.

**Files/shas.** `Q0Degree5ClosureExtension.lean`
`239a7498c6fd77d42f0db35a7bdaddf9becb5e5f491d52e24c5630afc616aa26`;
audit `audit_q0_degree5_closure_extension.py`
`3315f7d31a9ca29fb99217e65dbd0bf87699f162ee5921a7ab7ba914983a0730`;
report `q0-degree5-closure-extension-audit.json`
`68f8ace1f4bd94e367505a6259f6a354e6d994c7c632454bcacdd0a4f04b599b`.

**Checks (scope).** `py_compile` PASS; exact source/interface audit PASS,
including all eight new coordinate-transcription checks; `git diff --check`
PASS.  A Mathlib-only probe of the `Complex.arg` nonnegativity pattern timed
out at 120 s with no output, so there is **no local Lean verdict**.  The module
is CI pending, not paid.

**Still unproved.** All 11 face, 9 switch, and 9 closure-aware sector maxima;
the concrete strict source total (`canonicalTotalUpperQ < piLo`); q0(5,8)
exclusion; six other classes; energy; arbitrary-centre theorem.

**Next concrete step.** Build exact-rational interval/grid maxima for the
coordinate-dependent closure term in each sector on `a∈[0,π]`, `u,v∈[0,1]`,
then emit the concrete `ClosureFactorBounds` instance and check the strict
total.  First ask CI to kernel-check the new coordinate definitions in
`Q0Degree5ClosureExtension`.


## 2026-11-02 (session 184) -- source closure coordinate ranges

Verified the Lean coordinate transcription against `q0_closure_dual.py`: its
`ch=R*sqrt(...)`, `w=2*asin(ch/2)` is exactly our unnormalized chord followed
by `2*asin((19/50)*chord/2)`, and `R` cancels from both `atan2` angles.  Added
`sourceLeftBaseAngle_le_pi`, `sourceRightBaseAngle_le_pi`, and
`sourceSectorWidth_le_pi`; together with the prior nonnegativity lemmas these
give the box-domain range `[0,pi]` needed for finite maxima.

**Files/shas.** Lean `f0949ed18d6814d26e2413475ea00e0df8971d9457720145b157f64bfec32577`;
audit `5c6146219b14a8a0ce8cee25d61a7a4da4031ef801a84d0113a1971b17ce2e9a`.
Exact audit, `py_compile`, `git diff --check` PASS.  No Lean build/CI verdict:
new range declarations **CI pending**, not paid.  Still unproved: all 11 face,
9 switch and 9 closure-aware sector maxima; strict total; q0(5,8) exclusion;
six classes; energy; arbitrary-centre theorem.

**Next concrete step.** CI-check the ranges while emitting rational interval
bounds for the coordinate-dependent sector term, then compute the concrete
`ClosureFactorBounds` maxima and strict total.
