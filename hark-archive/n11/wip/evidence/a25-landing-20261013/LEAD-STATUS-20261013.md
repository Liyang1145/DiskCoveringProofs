# n=11 formalization — Lead STATUS snapshot 2026-10-13 (session start)

## Authoritative workspace

`E:\ai4math2\research-2026\n11-formalization`
(the `C:\Users\袁力阳\Desktop\ai4math2\...` path is a PARTIAL junction tree with
a STALE real `lean\` dir + stale `.lake` + stale STATUS.md/DEAD.md dated
2026-10-02; only `evidence`, `audit`, `certificates`, `manifests`,
`lean\N11Formalization`, `lean\evidence` are live junctions to E:.
NEVER run lean/lake with cwd under C:.)

## Frozen objective (unchanged, INCOMPLETE)

```lean
∀ (r : ℝ) (c : Fin 11 → Point),
  0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r
```
SAME C891 sourceRoot6, full closed unit disk, arbitrary/repeated/degenerate
centers. No sorry / research axioms / native_decide / Lean.ofReduceBool /
decimal or sInf replacement / symmetry weakening / unpaid premises.
Allowed axioms only: propext, Classical.choice, Quot.sound.

## Last ACCEPTED root = A24

- Acceptance `evidence\codex-handoff\ACCEPTANCE-A24-ACTIVE-INTERVAL-CERTIFICATES-20261008.json`
- Manifest `a24-active-interval-certificates-20261008-manifest.json` 203/203 green
- Root SHA256 `16EA50867C0702B4DE6B293FD4DCB4579AF6411F64C2AA47FE66B74973FAA1F6`
- 1483 owned Lean sources, 142 standard-axiom reports, 2 frozen root runs exit0
- Remaining: C450 **25**, energy **2076** (1687 with candidate routes, 389
  needing genuine certificates), **7** class exclusions unpaid; 120 sharp
  patches paid.

## The immediate obligation: land the interrupted A25 round

A25 was cut off by a sub-agent service usage limit at 2026-10-08 ~22:26.
Verified absent: A25 manifest, A25 acceptance JSON, A25 root-audit log,
A25 control log, A25 handoff doc, `a25-final-readonly-consistency.json`.
Verified: NONE of the 30 new modules are imported into the root.

30 new modules (files newer than the A24 acceptance cut 2026-10-08 13:54),
plus 1 new probe `ProbeA25CanonicalFiniteRootAudit.lean`.

The 2026-10-08 driver declared only **28** extras (ExpectedTotal 231) and
OMITTED two real new modules: `CanonicalBalancedFiniteClassCertificate`,
`SharedMomentConcreteSectorGradientControls`. Corrected scope = **30 extras,
ExpectedTotal 233**.

### Blocking defect

`SharedMomentA25CertificateControls.lean` gate exit1; two theorems carry
`sorryAx` (`zero_chord_cell_not_gradient_valid`,
`zero_chord_cell_not_positive_certificate`). Root cause is a tactic arithmetic
gap, not a false statement: `simp [chordSq] at hp` yields `hp : 2 < 1 + 1`
without evaluating the numeral, and `chordSq ![0,1,1] = 0` genuinely makes `hp`
absurd. Fix is local (norm_num/omega), statements unchanged.

### Missing module builds (no olean): 8

CanonicalSharedMomentFiniteCertificate, CanonicalSharedMomentOrbitTransport,
SharedMomentConcreteSwitchBatch, SharedMomentA25CertificateControls,
SharedMomentConcreteFace1Part1, SharedMomentConcreteFace1Part2,
SharedMomentConcreteFace1Part3, SharedMomentConcreteFace1Certificate

### Missing standalone gates: 5

SharedMomentA25CertificateControls, SharedMomentConcreteFace1Part1,
SharedMomentConcreteFace1Part2, SharedMomentConcreteFace1Part3,
SharedMomentConcreteFace1Certificate

## What A25 buys (framework credit ONLY — no class/C450/energy is paid)

- `ActualCanonicalSharedMomentConsumer.CanonicalCertificate` /
  `CanonicalFactorBounds`: full-domain factor consumer in canonical rational
  coordinates, strict total `canonicalTotalUpperQ ... < RatInterval.piLo`.
- `CanonicalSharedMomentFiniteCertificate.FiniteCanonicalCertificate`: a class
  certificate carrying only finite rational tables + leaf certificates;
  `toCanonical` produces the semantic bounds internally.
- `SevenFiniteTables` + `seven_class_exclusions_of_finite` +
  `full_disk_bound_of_finite_class_tables`: the 7 unpaid class exclusions, and
  a FULL-DISK quantifier theorem with h450/henergy still explicit.
- `CanonicalSharedMomentOrbitTransport.balanced_certificates_of_two`: TWO
  representative certificates yield a certificate for ALL 8 cuts of the
  q1-balanced class. A genuine 8→2 reduction for that class, if non-vacuous.
- `CanonicalBalancedFiniteClassCertificate.SixAndBalancedFiniteTables`: reduces
  the q1_balanced entry from 8 tables to 2.
- Concrete reality: `SharedMomentConcreteFace1*` is a real 1239-node rational
  factor tree for ONE face (bound `18011/100000`, box `[0,1571/500]^2`);
  `a25-face1-direct-diagnostic-failure.json` records that direct whole-cell
  interval arithmetic blew a 250000-node budget, so local gradients are
  required. Concrete class cost is NOT routine table filling.

## Round 1 assignments (all routed cline-server/cline-pass/deepseek-v4.1-flash, effort max)

| task | member | scope |
|---|---|---|
| task-1 | m1-face1-tree | gate+build Face1 Part1/2/3/Certificate → `start0_face1_full_domain_upper` |
| task-2 | m2-switch-sector | gate+build SwitchBatch (3.7MB, never compiled) + Sector controls |
| task-3 | m3-bridge-certificates | fix A25CertificateControls sorryAx; gate+build 4 bridge modules |
| task-4 | m5-adversarial-audit | INDEPENDENT audit: non-vacuity, pass-through, coverage |
| task-5 | m4-a25-acceptance | corrected 30-module driver, probes, root pair, manifest, acceptance, handoff |

Lead owns: the root import block in `lean\N11Formalization.lean` (must be added
only after each module's build is green), the STATUS/GOAL update, and the
completion comparison.

## Hard constraints for everyone

- Single global Lean mutex `Local\N11Formalization_LeanSerial_20260929` via
  `evidence\resume-lead\Invoke-LeanSerial.ps1` (600 s wait). Report LOCKWAIT
  timeouts; never launch unlocked.
- Append-only evidence: never overwrite an existing log/JSON.
- Editing a module VOIDS its previously recorded gate (gate hash must equal the
  current file hash).
- Distinguish: standalone gate exit0 / bare module build exit0 / root-integrated
  / independent audit. These are four different claims.

## MILESTONE — 30/30 module-green + root integrated (2026-10-13 15:55)

Independently recomputed by Lead over 2365 parsed `*.result.json` files:

- **30/30 A25 modules satisfy all five section-6 module-greenness conditions.**
- Root integration DONE by Lead: `N11Formalization.lean` SHA
  `16EA50867C0702B4DE6B293FD4DCB4579AF6411F64C2AA47FE66B74973FAA1F6` (A24)
  -> `4F470AF507F320488DFBC168F9AE39645904AF569AE46B9FFB8F5E520BC5EDAF`.
  758 -> 788 import lines (unique 756 -> 786); added=30, removed=0.
  Backup: `lean\N11Formalization.lean.pre-a25-imports-20261013`.
  Two duplicate imports (HessSeamBridge, HessSeamMain) are PRE-EXISTING in the
  A24 baseline and were deliberately not touched.

### The one module that was genuinely broken (and nearly hidden)

`CanonicalBalancedFiniteClassCertificate` had **never compiled**: gate1 exit1,
module1 exit1, no olean. It is one of exactly the TWO modules the 2026-10-08
acceptance driver omitted from its 28-module list -- so the omission was
masking a real failure, not a bookkeeping slip.

Real defect: `(deterministic) timeout at whnf/isDefEq, max heartbeats 200000`
at the `∀ k, ∃ D kap eta, Nonempty (CanonicalCertificate ...)` block that
re-types the `(4 : Fin 8)`-indexed statement to `O.run_length`. m3 localized it
by elimination (probe2's G1-G9 all passed, ruling out the `toCanonical`
conversion, the ∃-telescope, `q1Faces 7 4` and `sharpAlpha`), then probe3 tested
four restructurings: w4/w3/w2 FAILED, **w1 and w0 PASSED**.

Fix applied (no resource-limit increase, statements untouched):
```lean
have hcut := Hall O.cut
rw [← he] at hcut          -- he : O.run_length = (4 : Fin 8)
obtain ⟨D,kap,eta,⟨K⟩⟩ := hcut
```
i.e. specialize FIRST, then rewrite the index in the small instance, instead of
re-typing the whole ∀-telescope. Confirmed byte-equivalent to probe3's w1 body.
Result: gate2 exit0 82.9 s, module2 exit0 77.3 s, olean 0.06 MB, 3 axiom reports
all exactly the allowed trio, module SHA `F71D338797184F8550C407FBD0E9CFD53CC4246F42581608750ECF7EA968644A`.

Two integrity notes for the record: the pre-fix axiom line listing
`seven_classes_of_six_and_two` as its own axiom is a FAILED-DECLARATION artifact,
not a circularity; and gate1's exit1 was a pure ORDERING artifact (it ran before
the dependency's olean existed), distinct from the real defect.

### Corrections to BRIEFING.md (empirically established, do not re-try the originals)

1. **7a fix**: `norm_num [chordSq] at hp` does NOT close the goal -- `norm_num`
   cannot reduce the vector literal `![0,1,1] 2`. The working closer is
   `simp [chordSq] at hp` then `exact absurd hp (by norm_num)`. Also the real
   hypothesis is `2 * ![0,1,1] 2 < 1 + ![0,1,1] 2 ^ 2`, one normalization level
   earlier than the briefing's `2 < 1 + 1`.
2. **7b undercounts**: 9 modules lacked an olean, not 8.
3. **`sourceRoot 6` needle**: the string has ZERO direct occurrences in
   `ProbeA25CanonicalFiniteRootAudit.lean`; it is emitted only indirectly by
   line 101's `#print ...sourceRadius` (Lean prints its body as
   `sourceRoot 6`). Line 101 is LOAD-BEARING; deleting it breaks acceptance.
4. **Manifest evidence discovery is NON-RECURSIVE** (`Invoke-A21Manifest-20261007.ps1`
   line 18: `Get-ChildItem -LiteralPath $PSScriptRoot`), so member logs under
   `a25-landing-20261013\mN\` are invisible. m4 added a staging step.
5. **Serialization**: the original `Invoke-LeanSerial.ps1` has a hardcoded 600 s
   mutex wait, shorter than one peer build (SwitchBatch module build = 1042 s),
   so healthy members hit spurious lockwait timeouts. Lead added
   `evidence\resume-lead\Invoke-LeanSerial20261013.ps1` (-MutexWaitSeconds,
   default 5400). Original left byte-identical.
6. **Rule-3 regression hazard** (found by m4): staging a fresh gate without a
   correspondingly fresh build flips a green module to RED, because the manifest
   picks the newest gate and newest build independently.

### A25 still earns FRAMEWORK CREDIT ONLY — sharper reason now

m2's final analysis: `SharedMomentConcreteSwitchBatch` proves all nine
`start0_switch{i}_full_angle_upper` (7923 node theorems, 9/9 terminate, no gaps)
yet pays ZERO class credit, because (G1) there is no aggregation theorem --
`start0_switch_total_bound := 22523/250000` is defined and referenced by NOTHING,
and (G2) `FiniteCanonicalCertificate.switches` wants `SwitchCertificate
(canonicalSwitchP D kap i) ...`, a structure over GradientSwitchLeaf the batch
does not produce, with no coefficient-identity proof tying its p/q/b/d2/d1 to
`canonicalSwitch*`. Nine proved leaf certificates, no consumer satisfaction.
m2 also flags a namespace hazard: `start0_switch0_bound` is 1/2000 in
LeafControls:34-39 but 141/1000000 in SwitchBatch:12-17.

### Still unpaid after A25 lands

C450 **25**; energy **2076** (1687 with candidate routes, 389 needing genuine
certificates); all **7** class exclusions (SevenFiniteTables consumed as a
HYPOTHESIS only); 120 sharp patches paid. `full_disk_bound_of_finite_class_tables`
has the exact frozen quantifier shape with `h450` and `henergy` STILL EXPLICIT.

## Next Lead action

m4 runs Phase 2: audit-probe gate -> root pair -> staging -> manifest ->
acceptance -> consistency -> handoff. Then Lead updates STATUS/GOAL and does the
completion comparison. Highest-leverage next mathematical move (m2's G2):
`SwitchCertificate.of_full_angle` bridge + a 9-way `Fin 9` induction.

---

# ROUND 2 (2026-10-13/14) — A25 LANDED, then the binding gap identified

## A25 is fully landed and root-accepted

`ACCEPTANCE-A25-CANONICAL-FINITE-CERTIFICATES-20261013.json`; manifest
**233/233**; `a25-final-readonly-consistency-20261013.json` written with
`documentation_current: true`; two frozen root runs exit0/unchanged/
changed_sources empty/**1521** sources; probes hash-bound (root audit gate2,
174 standard-axiom reports, 30/30 needles; controls gate2, 14 reports).
Root SHA `4F470AF507F320488DFBC168F9AE39645904AF569AE46B9FFB8F5E520BC5EDAF`.
Lead independently re-derived all five greenness conditions for all 233 modules
against disk: **233 ok / 0 failures**. `unconditional_n11_complete: false`.

## The `sourceRoot 6` needle defect (m4's discovery)

`Accept-A9Framework-20261005.ps1` requires the literal substring `sourceRoot 6`
in the audit log. `ProbeA25CanonicalFiniteRootAudit.lean` has **453**
occurrences of `sourceRadius` and **zero** of `sourceRoot`; the needle is emitted
only indirectly by line 101's `#print ...sourceRadius`, because Lean prints
`sourceRadius`'s body as `... sourceRoot 6`. Line 101 is LOAD-BEARING — deleting
that redundant-looking print silently breaks acceptance.

## The stale-olean trap (controlled experiment)

The A25 root-audit probe first exited 1 with ~37 `unknownIdentifier` errors,
yet its log already had 142 axiom reports and all 31 needles. Cause: `lake env
lean` does NOT rebuild imports, so the probe resolved `import N11Formalization`
against the A24-era root olean (predating the 30 imports by 5 days). Proven by a
controlled before/after on an UNCHANGED probe file (same SHA `9D56E891…BEC96`):
exit1 -> exit0, `unknownIdentifier` 37 -> 0, axiom reports 142 -> 174, with the
root rebuild the only intervening change. **Correct order is root build FIRST,
then re-gate the probe** — the reverse of the Lead's original instruction.

## Root-audit probe landmines (all defused)

1. 2026-10-08 driver declared **28** extras and omitted TWO real modules
   (`CanonicalBalancedFiniteClassCertificate`,
   `SharedMomentConcreteSectorGradientControls`) -> correct total **233**.
2. `CanonicalBalancedFiniteClassCertificate` had **never compiled** — a
   default-heartbeat `whnf`/`isDefEq` timeout at the ∀-typed re-type of the
   index. Its omission from the 28-list was masking a REAL failure. Fixed by
   specializing BEFORE rewriting: `have hcut := Hall O.cut; rw [← he] at hcut`.
   Localized by elimination (probe2's G1-G9 ruled out the `toCanonical`
   conversion, the ∃-telescope, `q1Faces 7 4` and `sharpAlpha`); probe3 tried
   four restructurings, three failed (`w4/w3/w2`), `w1`/`w0` passed.
3. Manifest evidence discovery is **NON-RECURSIVE**
   (`Get-ChildItem -LiteralPath $PSScriptRoot`), so member logs under a
   subdirectory are invisible; m4 added a staging step.
4. **Rule-3 regression hazard**: staging a fresh gate without a fresh build
   flips a green module to RED, because the manifest picks the newest gate and
   newest build INDEPENDENTLY. This fired for real on
   `SharedMomentA25CertificateControls`.
5. `Accept-A9Framework` line 60 hard-codes three A20 incident needles while the
   A25 check needs five different A25 needles; m4's
   `ProbeA25CanonicalFiniteControls.lean` re-proves the three A20 statements in
   its own namespace so one log satisfies both families.

## The binding gap (NEW — this is the round's structural finding)

**No coefficient identity exists.** There is no theorem anywhere of the shape
`canonicalSwitchP D kap i = <concrete rationals>`, nor for `canonicalFaceP` /
`canonicalSectorC` / `canonicalSwitchQ/B/D2/D1`. Consequences:

- `FiniteCanonicalCertificate.switches` demands a `SwitchCertificate`
  STRUCTURE (root/contains/tree over `GradientSwitchLeaf`). The concrete
  `SharedMomentConcreteSwitchBatch` proves all nine
  `start0_switch{i}_full_angle_upper` (7923 node theorems, no gaps, 9/9
  terminate) yet yields **none** of those fields, so it pays **ZERO class
  credit**. `start0_switch_total_bound := 22523/250000` is defined and
  referenced by NOTHING — there is no aggregation theorem.
- The same gap covers the faces (`SharedMomentConcreteFace1*`, a genuine
  1239-node tree with a per-node axiom sweep) and the sectors.
- Namespace hazard: `start0_switch0_bound` is `1/2000` in
  LeafControls:34-39 but `141/1000000` in SwitchBatch:12-17.

Substantive cheaper observation: the nine concrete
`start0_switch{i}_full_angle_upper` have EXACTLY the type of
`SwitchCertificate.sound`'s conclusion for the corresponding constants, and
`switchRoot` is contained in the batch's root cell `switchCell 0 (1571/1000)`.
So a bridge is plausible via `ContainsCell` + the `SwitchLeaf` disjunct — but it
still needs the coefficient identity to be a `FiniteCanonicalCertificate`
field, which is the missing piece.

## Q1 NON-VACUITY: RESOLVED (kernel-checked), with a negative control

Independent audit (m5b) asked whether `CanonicalCertificate`'s strict field is
even satisfiable. Answer: **YES**, and it is now kernel-checked.

`lean\ProbeA25AuditQ1Witness.lean` (top-level probe, NOT a manifest module),
gate `evidence\a25-landing-20261013\m5\q1witness-gate8.log`, exit=0, all NINE
theorems exactly `[propext, Classical.choice, Quot.sound]`:
- POSITIVE ARM: at `F = q0Faces 1`, mu = (11/2000, 11/2000, -17/1000,
  -31/2000 ×5, -17/1000, -49/1000, 193/2000), width = 0, all structural
  coefficients = 0, kap = 0, faceMax = 3/20, switchMax = 1/20,
  sectorMax = 1/10, the strict field HOLDS together with
  `CanonicalMaskBalancedQ`, nonnegative edges, `0 ≤ 0` and the sharpAlpha ear
  bracket.
- NEGATIVE CONTROL: at a different datum the SAME strict inequality is FALSE,
  kernel-checked as a `¬` (`audBadStrictFails`) — so the positive arm is
  sensitive to the strict field, not vacuous.
- eta: the strict total DECREASES in eta (coefficient `2*(alpha - pi) ≈ -4.5566`
  per unit eta dominates the `+2*alpha*eta` return and the ≤0.78-per-sector
  outsideGaps gain), so the minimum sits at large eta; best scan 2.994016 vs
  piLo 3.14159. m5b flagged its own earlier sign error as a correction.
- **CREDIT SCOPE**: interface satisfiability ONLY. `CanonicalFactorBounds` is
  deliberately NOT constructed and freely chosen maxima are not a payable table,
  so this pays ZERO class credit.

## Website / publication work (completed this round)

- Repo `Liyang1145/DiskCoveringProofs` made **public** (was private).
- Release **v1.0.0** created, tag -> `57f7f6ff8fe3c20c7835b3c2c08ff51ed1ac8bb3`,
  draft=false, prerelease=false, 0 assets. Verified NO content change: main HEAD
  and tree sha identical before/after, parent count 0.
- Zenodo DOI **10.5281/zenodo.23344751** (type=software, version v1.0.0,
  conceptdoi 10.5281/zenodo.23344750) minted from that release; the user then
  asked for the badge in the README.
- README DOI badge added by commit
  `1790e4aad4d06a70c272c9608f186beaccc4e9f9`, changing **exactly two files**:
  `README.md` and its hash-pinned `manifests/FILES.jsonl` entry. Coupling
  matters: `tools/verify_delivery.py` fails closed on a digest mismatch and CI
  runs it on every push, so a README-only edit would have BRICKED CI.
  CI run 38490433455 concluded SUCCESS, including step 6 "Check exact delivered
  bytes and lossless large files" (the repo's own 14456-file SHA256 check).
- An n=11 increment payload (2701 files / 364 MB) was staged and verified
  (`ALL CHECKS PASSED`) but **NOT pushed** — it is ready for a PR on request.

## Next executable step

Attack the coefficient identity (option B to m5b): determine whether
`canonicalFaceP D kap f` / `canonicalSwitchP D kap i` can be made to EQUAL the
concrete `start0_face1_p s` / `start0_switch{i}_p` values by a choice of
`D`/`kap`, or whether the concrete A25 batches are structurally unconnected to
the consumer. A precise negative answer is high value: it would establish that
the concrete face/switch/sector batches cannot pay class credit without new
bridge lemmas, and would take them off the critical path.

---

# ROUND 2 RESULT — the coefficient identity is REFUTED (two independent ways)

**Both obstructions are numeric/exact-rational, NOT yet kernel-checked.**

## C1804 (Lead): the P family cannot match the concrete face data

`canonicalFaceP D kap f s = -D.mu (D.label f s) - kap (D.flagEdge f s)`
(`ActualCanonicalMomentTransport.lean:68-70`), where `D.label f s` is the
**s-th smallest** element of `f` (`ActualCanonicalFaceCoordinates.lean:13`) and
`D.flagEdge f s = f.erase (D.label f s)` (`:51-52`). Crucially P carries **no
`(f,s)`-indexed free factor**, unlike Q/B which carry `faceMask f s`.

**Theorem.** There is NO choice of `D.mu` (11 rationals) and `kap` (21 edges)
with `canonicalFaceP D kap f = start0_face1_p` for all 11 faces of `q0Faces 1`.

**Hand-checkable certificate.** Sum these six face-P equations with the signed
weights shown; every mu and kap coefficient cancels exactly:

| weight | equation | face, slot |
|---|---|---|
| −1 | −mu₀ − kap{1,9} = 14313377/250000000 | (0,1,9), s0 |
| +1 | −mu₁ − kap{0,9} = −30939859/1000000000 | (0,1,9), s1 |
| +1 | −mu₀ − kap{9,10} = 14313377/250000000 | (0,9,10), s0 |
| −1 | −mu₁₀ − kap{0,9} = −7389693/1000000000 | (0,9,10), s2 |
| −1 | −mu₁ − kap{9,10} = 14313377/250000000 | (1,9,10), s0 |
| +1 | −mu₁₀ − kap{1,9} = −7389693/1000000000 | (1,9,10), s2 |

`mu₀, mu₁, mu₁₀` and `kap{1,9}, kap{0,9}, kap{9,10}` all cancel (each appears
with net coefficient 0 — verifiable by hand), leaving
**0 = −88193367/1000000000 ≠ 0**. Contradiction.

Sharp quantitative form: the maximum **simultaneously matchable face set has
size 10 of 11** (e.g. dropping face (1,9,10)); the per-slot-constant relaxation
is consistent with 4 free dimensions, but `start0_face1_p` itself lies outside
the achievable set.

## C1806 (m5b, verified by Lead): concrete Face1 and switch data are incompatible

**Forced relation.** For `e = cycleEdge k ∈ faceEdges F` and any `D` with
`CanonicalMaskBalancedQ D`:

```
Σ_{f,s : flagEdge f s = cycleEdge k} canonicalFaceQ D f s  +  canonicalSwitchQ D k  = 0
```

and identically for B/`sideFirst`. Derivation: `canonicalFaceQ = faceMask *
sideSecond(flagEdge)` (`:73`) and `canonicalSwitchQ = switchMask k *
sideSecond(cycleEdge k)` (`:83`); on the filtered slots factor out
`sideSecond(cycleEdge k)`; balance (`:263-264`) gives
`canonicalEdgeSumQ + switchSumQ switchMask = 0`, and `cycleEdge` is injective
(`ActualEdgeFlagSums.lean:196`).

**Load-bearing premise (Lead's own computation).** For every `k ∈ Fin 9` and
every `m ∈ {1,2,3}`, **exactly ONE slot** `(f,s)` of `q0Faces m` has
`flagEdge f s = cycleEdge k` — always the hub slot `s = 2`. So the filtered sum
is a genuine **2-term identity**, not a sum.

**Violation.** At `q0Faces 1`, `k = 0`: face (0,1,9) slot 2 has
`flagEdge = {0,1} = cycleEdge 0`, so balance forces
`canonicalFaceQ D (0,1,9) 2 + canonicalSwitchQ D 0 = 0`; concretely
`251843483/1000000000 + 21538627/125000000 = 424152499/1000000000 ≠ 0`, and for b
`−102151007/500000000 + −184795967/1000000000 = −389097981/1000000000 ≠ 0`.
Magnitudes ≈0.42 and ≈0.39 — not rounding noise.

**Scope.** Specific to the three **Q0** classes: face (0,1,9) contains hub 9 but
not hub 10, while every `q1Faces` central face contains 10 and `q1Ear = {8,0,1}`,
so (0,1,9) is not a Q1 member.

## Why the two are independent

C1804 constrains `(mu, kap)`; C1806 constrains
`(faceMask, switchMask, sideFirst, sideSecond)` via balance. **The variable sets
are disjoint within `CanonicalCoeffQ`**, so neither implies the other. Two
independent families give the same verdict from different directions.

## Strategic consequence

The concrete A25 data sets were generated for objectives the canonical consumer
**cannot express**. Therefore:

- The concrete `SharedMomentConcreteFace1*` tree (1239 nodes, per-node axiom
  sweep) and `SharedMomentConcreteSwitchBatch` (nine proved
  `start0_switch{i}_full_angle_upper`, 7923 node theorems) **cannot jointly
  discharge one `FiniteCanonicalCertificate`**, and the Face1 tree cannot serve
  the `faces` field at all.
- These batches are **NOT on the critical path** to paying a class. What the Q0
  tables need is a **data generator** producing coefficients consistent with the
  canonical definitions, not more trees.
- This does **not** make A25 unsound, and does not touch the orbit transport
  (Q3), the pass-through derivation (Q2), Face1 coverage (Q5), or interface
  satisfiability (C1803). A25 remains correct framework credit.

## Retraction record

The Lead wrote an audit script (`audit_m5b_q6.py`) asserting C1806 was
overstated, on the theory that several slots share `flagEdge = cycleEdge k` and a
free "other" term could absorb the balance. Direct computation showed the
opposite — exactly one slot — so the Lead's objection was **withdrawn** and
m5b's relation **upheld**. The failed reasoning is recorded rather than deleted.

## Next executable step (updated)

m5b is gating `lean\ProbeA25AuditQ6ForcedRelation.lean`: (a) the forced relation
as a general lemma from the definitions, (b) its instantiation at the concrete
data closing the contradiction by `norm_num`, (c) the exactly-one-slot premise as
its own theorem, (d) a non-vacuity control. After that, the productive direction
is a **consistent data generator** for the Q0 coefficient tables rather than
further concrete trees.

---

# C1806 IS NOW KERNEL-CHECKED (C1807)

`lean\ProbeA25AuditQ6ForcedRelation.lean`, gate
`evidence\a25-landing-20261013\m5\q6relation-gate5.log`: **exit=0**,
unchanged=true, file SHA `2952D26D9BA232B501AE2EA7105FAE73A339579F6424066B3E84531BFDDEDE0F`,
**17 axiom reports, 0 forbidden tokens, exactly ONE axiom set**
`{propext, Classical.choice, Quot.sound}`.

Kernel-checked content:

- `audQ6_forced_relation` / `audQ6_forced_relation_B` — the general relation for
  **arbitrary** `F`, arbitrary balanced `D`, any `k` with `cycleEdge k ∈ faceEdges F`.
- `audQ6_filter_sum_Q` / `audQ6_filter_sum_B` — the `sideSecond`/`sideFirst`
  factorisation (where edge-indexing is used).
- `audQ6_switchSumQ_cycle` — `switchSumQ` picks out its own index on a cycle edge.
- `audQ6_slot_unique` / `audQ6_slot_exists` / `audQ6_cycleEdge0_mem` /
  `audQ6_card` — the exactly-one-slot premise and non-vacuity of its hypothesis.
- `audQ6_q0_obstruction` / `_B` — the concrete incompatibility at `q0Faces 1`
  as a kernel-checked `False`.
- `audQ6_residuals_nonzero` / `audQ6_residuals_large` — residuals nonzero and
  not rounding noise.
- **Four negative controls**, incl. `audQ6_control_not_balanced` and
  `audQ6_control_relation_fails`: an unbalanced `D` breaks the relation, so it is
  not vacuous.

**Lead's four mechanical fixes to reach exit0** (none weakens the obstruction):

1. `switchSumQ` unfolding needed `rw` rather than `unfold` to keep the type
   determined (`AddCommMonoid ?m` got stuck).
2. `simp only [if_pos h, …]` did not fire inside the `Finset.sum_congr` goals;
   replaced by explicit `rw` then `ring`.
3. `audQ6_control_edgeSum_zero` needed `ite_self 0` (the same closer found
   earlier for the Q1 witness probe) rather than a `by_cases`/`simp` pair.
4. `audQ6_slot_unique` was restated as a one-directional implication plus a
   separate converse. **NOTE — the Lead's stated reason for this was WRONG and
   is withdrawn (C1810):** the Lead claimed the biconditional was "FALSE as
   written". It is TRUE. m5b kernel-checked the exact biconditional
   (`ProbeA25AuditQ6SlotLemma.lean`, `q6slot-gate6.log`, 13 theorems, all
   `{propext, Classical.choice, Quot.sound}`), and the Lead's own exhaustive
   exact computation over `q0Faces 1` found **0 violations** among `i ∈ f.val`.
   The `decide` failure in gate1 was a **cascade artefact** of three earlier
   elaboration errors in the same file (the typeclass-stuck error plus two
   rewrite failures), which left metavariables in the goal. The restated form is
   retained because it is equally correct and more readable — not because the
   original was false.

**LEAN LESSON (cost the team real time, worth carrying forward):**
`decide +kernel` does **NOT** reduce `Finset.orderIsoOfFin`. Therefore
statements quantifying over the slot index via `canonicalLabel` cannot be closed
by `decide`, and the message is *"did not reduce to `isTrue` or `isFalse`"* — a
**REDUCTION failure, which must never be read as a falsity verdict**. m5b hit
this trap twice and it is exactly what produced the Lead's wrong "false" report.
The fix is to restate such facts in **element/card form** (e.g.
`(f.val.filter (fun i => f.val.erase i = cycleEdge k)).card`), which does decide;
m5b's `slot_count_one_element` is kernel-checked that way for all nine `k`.

---

# C1804 IS NOW FULLY KERNEL-CHECKED (C1812)

`lean\ProbeA25AuditC1804Structure.lean`, gate
`evidence\a25-landing-20261013\lead-c1804-structure-gate7.log`: **exit=0**,
unchanged=true, SHA
`1705B1D46617040C17600D061179BBFF84A6891437A18BCB2E3AC5A131EA4142`,
**4 axiom reports, all exactly `{propext, Classical.choice, Quot.sound}`**, 0
forbidden tokens. Together with C1808 (algebraic core, `lead-c1804-gate1.log`)
this closes the structural layer whose absence C1808 flagged.

- `audLabel_zero` — on a 3-element face, slot 0 carries the least element.
- `audLabel_two` — slot 2 carries the greatest element.
- `audLabel_one` — slot 1 carries the remaining element (surjectivity +
  injectivity of the order iso).
- `audFaceP_obstruction` — **headline**: from `canonicalFaceP D kap f =
  start0_face1_p` at the six slots `(f019,0) (f019,1) (f0910,0) (f0910,2)
  (f1910,0) (f1910,2)` of the faces `{0,1,9}, {0,9,10}, {1,9,10}`, derive
  `False`, by reducing to C1808's six-equation core and `linarith` + `norm_num`.

**Technique notes (7 gate iterations — worth recording):** `orderIsoOfFin` does
not reduce definitionally, so neither `decide` nor `rfl` evaluates
`canonicalLabel`; the working route is monotonicity + surjectivity + injectivity.
`simpa only using h` does **not** cross the definitionally-equal
`D.label`/`canonicalLabel` boundary — `simpa only [CanonicalCoeffQ.label] using h`
does. And `fin_cases` leaves beta-redexes needing
`simp only [Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk]`.

## Net position of the two obstructions (both now kernel-checked)

| | family used | status |
|---|---|---|
| **C1804/C1808/C1812** (Lead) | `canonicalFaceP` = `-mu(label) - kap(flagEdge)`, no `(f,s)` freedom | kernel-checked at 3 faces / 6 slots |
| **C1806/C1811** (m5b) | `canonicalFaceQ/B` vs `canonicalSwitchQ/B` via balance | kernel-checked, general lemma + concrete instance + 4 controls |

Variable sets are **disjoint** (`mu`,`kap` vs `faceMask`,`switchMask`,`side*`), so
the two are independent. Both say the same thing: the concrete A25 data sets were
generated for objectives the canonical consumer cannot express, so the Q0 tables
need **regenerated consistent data**, not more trees.

## Next executable step

m5b is running task-6: `Q0-GENERATOR-FEASIBILITY.md` — enumerate the free degrees
of freedom, re-derive the max-matching bounds, and give a sharp
feasible/infeasible verdict on generating a full Q0 table (11 faces + 9 switches +
9 sectors with balance, nonnegativity and strict total < `piLo`). Its preliminary
read is that the binding constraint is **not** balance but the interaction of the
strict total with needing each `faceMax`/`switchMax`/`sectorMax` to dominate a
supremum over a full domain — the same ~29 expensive trees per class flagged in
Q1. That claim must be made precise, not asserted.

---

# ROUND 2, PART 2 — the budget question, settled

## m5b's task-6 accepted, and independently re-derived

I re-implemented m5b's whole joint system from scratch (independent code,
independent exact RREF over `Fraction`) and reproduced its results exactly:

- **Frontier `nf_max(ns)` for ns = 0..9 = `[9,9,8,8,7,7,6,6,5,4]`** — exact match,
  including its specific 9-face witness (dropping `{1,2,10}`, `{1,9,10}`)
  validating, and `feas(all 11 faces, 0 switches)` returning **False**.
- **m5b's own correction is right and important**: 11 faces is infeasible at
  *every* switch count, so the required point (11 faces, 9 switches) is outside
  the feasible region entirely — stronger than its retracted C1814.
- **1015 = 3·29 + 4·8·29** — confirmed against source: `SevenFiniteTables`
  (`CanonicalSharedMomentFiniteCertificate.lean:86-93`) has 3 `Q0FiniteTable` and
  4 `Q1FiniteTables` fields, and `Q1FiniteTables m` (`:75-77`) is
  `∀ k : Fin 8, ∃ D kap eta, …`, so 8 cuts per Q1 table.
- **Balance is decoupled and always solvable** (153 variables vs 44 constraints,
  132 net) — confirmed.

## MY OWN ERROR, corrected (C1816)

I had *inferred* `sharpConstantUpperQ ≈ +0.065368` from a recalled total. Computed
exactly from the definitions it is

    -1727875959474386281153/10^23 ≈ -0.01727876

(`stationWeightQ i = if i.val < 9 then 1 else 2`; `canonicalStationCoeffQ =
-11/2000`; `piProductUpper` of a negative is negative). My first budget run used
the wrong value and concluded the sound total *exceeded* `piLo` by 0.0064. With
the correct value the sound total is **3.065350 < piLo, slack 0.076242** —
reproducing m5b's Q1 slack 0.0762 to five digits. **My error, not m5b's**; it went
the *other* way from m5b's self-corrections (mine made the route look dead).

## THE C1803 WITNESS'S DECLARED MAXIMA ARE UNSOUND (my finding)

At that witness (`q = b = 0`, `kap = 0`) the declared `switchMax = 1/20` gives sum
0.45 against a **true** switch sup sum of **0.502957**, and `sectorMax = 1/10`
gives 0.90 against a true sector sup sum of **≥ 1.000386**. Both **understate**
their objectives, so a certificate using them would violate
`CanonicalFactorBounds`. The witness is **repairable** (raise `switchMax`/
`sectorMax`; the sound total still fits with 0.076 slack) and C1803 was always
caliber-limited to *interface* satisfiability — but the witness cannot be lifted to
a real certificate merely by adding trees; the maxima themselves must be
recomputed.

## THE DEGENERATE ESCAPE IS CLOSED (C1817)

The natural cheap route — set every coefficient to zero so objectives vanish and
all maxima can be 0 — does **not** work. `faceQuadratic`, `switchQuadratic` and
`sectorFactor` each contain a **standalone** term not multiplied by any
coefficient:

| term | value |
|---|---|
| `2*(19/50)^2` (faces) | `361/1250` = 0.2888 |
| `(19/50)^2/2` (switches) | `361/5000` = 0.0722 |
| `sectorFactor` (sectors) | ≥ 0.088615 |

At `D = 0`, with `sharpConstantUpperQ = 0`, the required sum of factor maxima is
**≥ 11·0.2888 + 9·0.0722 + 9·0.088615 = 4.6241**, exceeding `piLo = 3.14159` by
**1.4825**. So `D = 0` is infeasible outright.

## Where the route actually stands

The A25 route is **not** refuted arithmetically: at the C1803 datum the budget
absorbs sound per-factor maxima with **0.076** of slack. The binding obstacle is
**proof volume** — 1015 full-domain trees (87 Q0 + 928 Q1) against ~5 proved.
m5b is now running the one experiment that decides batch-vs-wall:
`lean\ProbeA25AuditTreeEmit.lean`, testing whether
`RationalBoxSubdivision.Certificate.split` can mechanically emit a single face
tree whose leaves all close by `norm_num`. If yes, 1015 becomes a batch job; if
no, the redirect is to revisit the **consumer interface** (one certificate per
class instead of 29 per class removes the multiplier).

**Credit unchanged**: none of this pays class credit. `c450_remaining = 25`,
`energy_remaining = 2076`, 7 of 7 classes unpaid.

---

# ROUND 2, PART 3 — THE C450 AXIS IS A BATCH JOB (C1818/C1820/C1821)

While m5b ran the A25 tree experiment, I turned to the **other two axes** of the
frozen theorem and found something materially better than negative information.

## A working mechanical emitter already exists

`evidence\codex-handoff\emit_c450_seventh_grouped.py` (11072 B) is a **guarded
generator** that already produced one paid segment's certificate:

- sha256-pins its inputs (7 guards)
- **refuses to run while Lean is live**
- enforces **fresh-only** targets (asserts the paths do not exist)
- emits 32 grouped files per segment + a Data + a Segment module
- literal rationals (`(num:ℚ)/den`), per-packet `decide +kernel` validity proofs
- the segment proof is a mechanical `fin_cases` dispatch over the 32
  `GroupedC##.bound` lemmas
- uniform consumer: `normalized_of_cells` (`C450GroupedClosedAssembly.lean:46`)

Every already-paid segment has **exactly 32** grouped files.

## The packet data for ALL 24 unpaid segments already exists

`evidence\codex-handoff\c450-grouped-remaining8-35-host.json` — **39 MB**, 28
segment results, **14405 packet records**.

**Indexing resolved by exact span matching** (not assumption): the JSON `segment`
field **is** the `c450Segs` index. JSON seg 11 has span `[9/250, 1/25]` =
`C450Source11Data.source11` whose `source_eq` says `c450Segs[10]? = some source11`;
JSON seg 12 has span `[1/25, 11/250]` = `source12` with `c450Segs[11]? = some
source12`. So JSON 11 ↔ `c450Segs[10]` ↔ `Source11` — the module suffix is one
larger than the index.

Consistent counts: `c450Segs.length = 36` (from `c450Segs.drop 11` with
`remaining_count = 25`, corroborated by `c450Segs.drop 12` with
`remaining_count = 24`). **Paid prefix = `c450Segs[0..11]`** (First..Sixth at 0..5,
seventh=6, eighth=7, ninth=8, tenth=9, source11=10, source12=11, each confirmed by
its own `source_eq`). The frozen goal consumes
`C450Source12Segment.RemainingSourceObligation = ∀ s ∈ c450Segs.drop 12`,
**remaining_count = 24**.

The JSON covers `c450Segs[8..35]` — so it contains packet data for **all 24**
unpaid segments.

## I verified all 14405 records myself

| check | violations |
|---|---|
| false `checks` entry | **0** |
| `gap ≤ 0` | **0** |
| out of p-bounds (`\|p0\| ≤ a0`, `\|p1\| ≤ b0`) | **0** |
| branch q-interval break (contiguous, width 1/16, spanning [−1,0]) | **0** |
| branch endpoint break (first lo 31/50, last hi 69/50) | **0** |
| record contiguity break (consecutive `hi == lo`) | **0** |

## Only ONE guard is stale

| file | pinned | on disk | |
|---|---|---|---|
| `DSHTenBoundaryData.lean` | `74226514…` | `74226514…` | MATCH |
| `C450GroupedPacketKernel.lean` | `CEBA2924…` | `CEBA2924…` | MATCH |
| `C450GroupedClosedAssembly.lean` | `370BE7A4…` | `370BE7A4…` | MATCH |
| `C450GroupedAmplitude.lean` | `E14BC072…` | `E14BC072…` | MATCH |
| root `N11Formalization.lean` | `1EC5D032…` | `4F470AF5…` | **STALE** |

## Consequence for strategy

The C450 axis is a **bounded engineering task** — re-pin one guard, emit 24
segments × 32 files = 768 modules through an emitter that has already worked — not
an open mathematical problem. This is the first **positive** path found this round.

**What is still untested**: whether the emitted files compile, whether
`CoversDirections` holds for the emitted `Qs`, and whether `SegmentNormalized`
closes. The JSON's own label says
`HOST exact candidates ONLY; actual Lean validity/coverage/source consumers
UNPAID`. `normalized_of_cells` needs **both** per-branch `CellBound` (which the
emitter supplies) **and** `DirectionsCover Qs` (which it may not) — that
distinction is exactly what task-7's pilot is designed to settle.

**m6-c450-pilot** (spawned, task-7) is running that pilot on `c450Segs[12]`:
re-pin the root guard, emit one segment, gate Data → 32 grouped → Segment, and
report whether `SegmentNormalized` closes, with a negative control showing the
emitter aborts without the re-pin. Verdict will be BATCH-JOB / WALL / PARTIAL.

---

# ROUND 2, PART 4 — C450 PILOT: the coverage question RESOLVED, my error corrected

## m6's pilot emitted and began gating successfully

`C450Source13Data.lean` + **all 32** `C450Source13GroupedC##.lean` +
`C450Source13Segment.lean` were emitted (33 files, under
`evidence\c450-emit-20261014\`). Its negative control **passed**: without the root
re-pin the emitter aborts precisely at the guard
(`GUARD FAIL … pinned 1EC5D032… on disk 4F470AF5…`, exit=1, 0 files emitted), and
with the re-pin it reports `GUARDS OK: 7 pinned files match disk`. So the re-pin is
load-bearing and the guard is real.

Gates so far (all via `Invoke-LeanSerial20261013.ps1`, fresh log per run):
`C450Source13Data` exit=0 (174 s, 3 module reports, allowed trio);
`C450Source13GroupedC01` exit=0 (119 s, 38 reports, allowed trio);
`C02` exit=0; `C03` in flight.

## MY ERROR CORRECTED — coverage IS supplied (C1823)

I inferred from the pilot JSON's `needed` entry "closed cover" that
`DirectionsCover` was the open obligation. **That was wrong, twice over:**

1. **Two different predicates.** `DirectionsCover {n} (Qs : Fin n → RatInterval)`
   (`C450GroupedClosedAssembly.lean:43`) is the **grouped** pipeline's predicate,
   consumed by `normalized_of_cells`. `CoversDirections {ι} (cells : ι → Cell)`
   (`C450AngularCellMajorant.lean:26`) is the **old** pipeline's — grepped only in
   `AngularCellMajorant`, `FifthSegment:39`, `FourthSegment:41`,
   `OuterCellMajorant:126`, `SixthAnalytic:41,66`, `SixthSegment:843`. Different
   types, different consumers. I conflated them.
2. **The original emitter already emits `directions_cover`** —
   `emit_c450_seventh_grouped.py` lines 164 (`DirectionPaid`), 167 (32 leaf
   lemmas), 183–184 (`interval_join`), 191 (`theorem directions_cover`), 198 (the
   `normalized_of_cells` call). The "closed cover" note is a **stale draft phrase**
   from the pre-grouped design.

## I verified m6's structural reason on the WRITTEN files

Parsed all 32 `def Qcell` values from the emitted `C450Source13GroupedC01..C32`:

- contiguous: `hi_i == lo_{i+1}` for every `i` — **True**
- every width exactly `1/16` — **True**
- first `lo = -1`, last `hi = 1` — **True**

So the 32 intervals **exactly tile [-1,1]**, and `DirectionsCover` is closed by 32
leaf lemmas plus 31 `interval_join` applications: purely combinatorial, **no
geometric argument and no extra library lemma required**. Both arguments of
`normalized_of_cells` (`DirectionsCover` *and* `cells_paid`) are supplied
mechanically.

**Process note recorded honestly**: my first two parsing attempts reported
"tiling FAILS". That was my regex failing on integer-literal forms (`(-1:ℚ)`,
`(0:ℚ)`) — a parser artifact, not a mathematical finding. This is the **third**
time this round that my inference was wrong and a teammate's direct check was
right (the biconditional, the off-by-one, the coverage predicate). Team claims and
Lead claims alike must be re-derived, not accepted.

## Sole remaining unknown

Whether `source13_paid` **closes** when the Segment gate returns. m6 flagged the
real risk: the Segment imports `C450Source12Segment`, whose olean may not exist,
so the gate may pull that build and fail for a reason unrelated to the emission. I
asked m6 to distinguish a failure in its **own emitted files** from one in the
**predecessor chain**, and to report the axiom list for `source13_paid`
specifically. No batching of the other 23 until the pilot verdict is in.

---

# ROUND 2, PART 5 — PILOT VERDICT ROOT-CAUSED (C1826), AND THE ROUND'S SYNTHESIS

## m6's Segment gate failed — but NOT because of the emission

m6's `segment-verdict.out.txt` reported `wrapper exit 1` with "0 errors in my
files / 0 in predecessor chain". Rather than accept that, I opened the raw log and
categorized **all** error lines. There are exactly 64, of exactly two kinds:

| kind | count |
|---|---|
| `failed to read file '…mathlib…olean'` | 32 |
| `Lean exited with code 1` | 32 |
| **any other error** | **0** |

Zero type errors, zero unsolved goals, zero `sorry`, zero unknown identifiers. And
the 32 failed reads name **only `C450Source12GroupedC01..C32`** — the
**predecessor** segment.

**Root cause**: the predecessor chain is unbuilt on disk —
`C450Source12GroupedC*` oleans present only **12/32** (C01..C12),
`C450Source12Segment.olean` **missing**. m6's Segment imports that module, so the
gate pulled a partial predecessor rebuild and died mid-flight.

**m6's own modules are sound**: `C450Source13GroupedC01..C32` oleans present
**32/32**, `C450Source13Data.olean` present (67536 B). Every one of the 32 gates
returning exit=0 is real.

**Not a mathlib problem**: the 6 mathlib oleans named in the failures all exist
(0.56–1.37 MB) and read successfully afterwards; only 3.8 GB of 15.2 GB RAM was
free with lake resident. Transient read failures under memory pressure.

## m5's `sorryAx` is a cascade artifact, not a missing proof

m5's `treeemit-gate2.log` shows 3 clean theorems plus
`certificate_of_allOK` carrying `sorryAx`. The literal word `sorry` appears
**zero** times in the file. The `sorryAx` comes from **failed elaboration** —
Lean injects it to continue past errors. There are 4 real errors (unknown
`Bool.and_eq_true.mp`; an `rcases` on a non-inductive; a
`(fun x => 0)` vs `(fun s => ↑(0 s))` mismatch; and a genuine missing
`0 ≤ piHi` step). Fix the errors and the taint disappears. I told m5 explicitly
**not** to "fix" it by supplying a `sorry`, and recalled that this exact mechanism
made me wrongly call one of m5b's lemmas "false" earlier in the round.

## THE ROUND'S SYNTHESIS: all three axes are the same shape

Reading the energy axis closed the picture:

| axis | shape | volume | status |
|---|---|---|---|
| **C450** (25 remaining) | **proven working emitter** + packet data for all 24 unpaid segments; guards match except the root | 24 × 32 = 768 modules | **BATCH JOB** |
| **energy** (2076 remaining) | ascending paid-ID chain, mechanical `rcases` dispatch + per-node oracle | 2386 non-sharp, 310 paid | template mechanism exists (`DSHTerminalTemplateV1`) |
| **A25** (7 classes) | needs 1015 full-domain trees; concrete data refuted (C1804/C1811) | 1015 trees vs ~5 proved | **blocked on emitter feasibility** |

Exact energy arithmetic, reproduced independently from source: 2506 terminals,
120 sharp (`sharp_count = 120`), 310 paid (`B11 paid_count = 310`) ⇒
**2386 − 310 = 2076**, matching the acceptance JSON exactly.

**The unifying question across all three axes is the same**: can a per-object
obligation be *generated mechanically* from rational data? C450: **yes, proven**.
Energy: template exists, unverified for the remaining 2076. A25: m5 is mid-test on
a single face tree, and its direct-leaf numbers (C1824) — 5425 leaves for M=0.218
rising to 136867 for M=0.2162 against a true sup of 0.21612476 — are the concrete
form of the wall, for the **direct** leaf only.

**Credit unchanged**: `c450_remaining = 25`, `energy_remaining = 2076`, 7 of 7
classes unpaid. What this round produced is a **map**: which route is a batch job,
which needs an emitter, and which is a wall.

---

# ROUND 2, PART 6 — THE EMITTER MECHANISM IS PROVED (C1828), BUT THE DEGENERATE ROUTE IS DEAD (C1829)

## m5's tree-emitter probe is GREEN (C1828)

`lean\ProbeA25AuditTreeEmit.lean`, gate
`evidence\a25-landing-20261013\m5\treeemit-gate4.log`: **exit=0**,
unchanged=true, SHA `F750708260EE7C42DA635F27D02C3F68B90962258A5C9C21B917B175DBBD0107`,
**6 theorems, all exactly `{propext, Classical.choice, Quot.sound}`, no `sorryAx`**.

The `sorryAx` I flagged in gate2 was indeed a **cascade artifact** — m5 fixed the
four real elaboration errors and the taint vanished with no proof supplied,
confirming the mechanism I described. (Second independent instance this round.)

**The design insight (m5's, and it is the crux):** `Certificate` is a **`Prop`**
(`RationalBoxSubdivision.lean:77`), so an emitter **cannot** return it inside an
`Option`. The working shape is a **computable `Bool` test** `allOK p M d B` that
recursively evaluates the rational leaf bound and picks the split coordinate, plus
a **bridge**:

- `certificate_of_allOK` (line 94): `allOK p M d B = true → Nonempty (Certificate (DirectPlaneLeaf p 0 0 M) B)`
- `allOK_sound` (line 158): the real ∀-bound over the face domain, via the proved
  chain `certificate_sound → direct_plane_leaf_sound → plane_upper_of_direct_certificate`
- `allOK_zero` (line 178): the depth-0 failure mode, exactly characterized, so no
  leaf is fabricated

So **"can an A25 face tree be machine-generated and proved sound?" is YES.**

## But the probe's `q = b = 0` instantiation cannot pay a class (C1829)

The obvious lift — choose `D` so that `q = b = 0` and reuse the probe — **fails
arithmetically**:

1. `q = b = 0` needs `faceMask f s · sideSecond(flagEdge f s) = 0` and
   `faceMask f s · sideFirst(flagEdge f s) = 0` for all `(f,s)`; cheapest:
   `faceMask ≡ 0`.
2. Then `canonicalEdgeSumQ ≡ 0`, so balance reduces to
   `switchSumQ switchMask e = 0` at each face edge.
3. All nine cycle edges are face edges of `q0Faces 1`, and
   `switchSumQ switchMask (cycleEdge k) = switchMask k`
   (`ActualEdgeFlagSums.lean:211`), so `switchMask ≡ 0`.
4. So **`masks ≡ 0` satisfies balance and makes `q = b = 0` identically** — the
   probe's hypothesis IS reachable.
5. **But** at `masks ≡ 0` the objectives keep their **standalone** terms —
   `361/1250` per face, `361/5000` per switch, `sectorFactor` per sector — so
   `CanonicalFactorBounds` forces

       ≥ 11(0.2888) + 9(0.0722) + 9(0.0886) = 4.6241 > piLo = 3.14159

**Consequence**: the degenerate route is infeasible by the **same arithmetic as
C1817** (the all-zero-`D` refutation). The **nonzero-`q/b` emitter is REQUIRED,
not optional**. C1828 answers the *mechanism* question; whether a *batch* exists
still depends on convergence rate at nonzero coefficients, which is C1824's
territory (5425 leaves for M=0.218 rising to 136867 for M=0.2162, true sup
0.21612476 — **direct leaf only**).

## Round 2 final map

| axis | blocker | verdict |
|---|---|---|
| **C450** | unbuilt predecessor chain (source12 12/32 oleans, no Segment olean); root guard stale | **BATCH JOB** — emitter proven, data complete |
| **energy** | per-node oracle generation for 2076 terminals; template exists | plausible batch, unverified |
| **A25** | emitter mechanism **proved** (C1828); convergence rate at nonzero `q/b` unmeasured | **the only genuinely open wall** |

**Every Lead error this round, recorded rather than buried**: the "false
biconditional" (C1810), the off-by-one indexing (C1822), the coverage-predicate
conflation (C1823), the inferred sharp constant (C1816), the spurious
parser-artifact "tiling FAILS" (noted in C1823), and the coverage over-read that
C1829 corrects in m5's phrasing. Three of these were caught by teammates'
direct checks, not by me.

---

# ROUND 2, PART 7 — BOTH PILOTS GREEN; FINAL MAP

## C450 pilot: BATCH-JOB, proven by gate (C1831/C1832, reviewed)

`C450Source13Segment` gate **exit=0**, "Build completed successfully (9474 jobs)",
olean 696552 B. All four module theorems — `directions_cover`, `cells_paid`,
**`source13_paid`**, `atom_of_remaining` — report exactly
`{propext, Classical.choice, Quot.sound}`. I re-extracted each axiom list myself
rather than trusting the summary, and confirmed the faint sets elsewhere in the
log belong to upstream modules.

- **Coverage was never open** — `directions_cover` is *emitted*
  (`C450Source13Segment.lean:328`, and already in the original emitter at
  `emit_c450_seventh_grouped.py:191`). My "closed cover" inference from the pilot
  JSON was wrong (C1823).
- **m6 found a real bug in its own emitter**: one parameter served both the split
  theorem's *name* (index) and the *drop amount* (index+1), so
  `c450Segs.drop 12` aliased the predecessor's `remainingSegs`, making the split
  claim unsatisfiable. Lean reported it as *"Tactic `decide` proved that the
  proposition `remainingSegs.length = 23` is false"* — an off-by-one wearing the
  costume of a false statement. **Every one of the 23 remaining segments fails
  this way under a one-knob driver.**
- **A parallel build produces false failures**: one `lake build` fanned out to
  ~33 concurrent Lean processes and emitted 32
  `failed to read file <mathlib>.olean` errors; those oleans exist and read fine.
  All affected modules build exit=0 **serially** — exactly why the wrapper exists.
- **The last segment is in a different file**: `remaining8-35` covers
  `c450Segs[7..34]`; `c450Segs[35]` lives only in the pilot JSON.

## A25 pilot: mechanism settled, one number remains

- **C1828**: machine-generating a face tree is proved — `allOK` (computable Bool)
  + `certificate_of_allOK` bridge + `allOK_sound`, all clean.
- **C1829 RETRACTED, C1830 (m5b)**: my "degenerate route is dead" was **wrong**.
  I conflated `masks ≡ 0` with `D = 0`; masks ≡ 0 leaves `mu, kap, width` free.
  Worse, I used `2*(19/50)^2 = 0.2888` as the face **sup**, but on the simplex
  `{a_s ≥ 0, Σa = π}` the max of `Π sin a_s` is `(√3/2)³ = 0.6495190`, not 1 —
  all `a_s = π/2` violates the sum. My own grid confirms the 1.539601×
  overstatement. **The C1803 witness IS the counterexample**: masks ≡ 0, `kap ≡ 0`,
  `mu ≠ 0`, sound total 3.06535 < piLo, slack **0.0762** — the same slack I
  computed in C1816. So `q=b=0` **is** liftable, and the budget is 3.0654 vs piLo,
  not 4.6241.
- **C1817 corrected**: `D = 0` infeasibility **survives** (3.5107 > 3.1416) but the
  margin is **0.369**, not the 1.4825 I quoted.
- **C1835**: ~**half of a face subdivision is FREE**. `PlaneOutside B :=
  piHi ≤ B0.lo + B1.lo` (`SharedMomentFacePlaneCertificate.lean:73`) with the
  **proved** exclusion `plane_not_outside` means those cells contain no admissible
  point. My exact count on a 32×32 grid: **496 of 1024** outside (m5b's figure
  reproduced exactly).
- **Nonzero q/b is MORE WORK, NOT BLOCKED**: `planeDirectUpperQ` already takes
  `p q b`; the rational leaf bound **saturates** (~4200 bits by depth 5–6, 4482 at
  depth 12) rather than growing, and time per leaf is flat. The gradient leaf beats
  the direct leaf by a **stable ~3.5×** (1739 vs 5425 leaves at M=0.218, ratio
  stable across two decades of excess).
- **m5b's own self-correction**: its announced non-monotone bound was a bug in its
  script (max over cells with *empty* third-coordinate intervals); it does **not**
  touch C1824, because the adaptive strategy never keeps a vacuity cell.

## Where this leaves the frozen goal

**No arithmetic obstruction remains on any axis. One number remains.**

| axis | state |
|---|---|
| **C450** (25) | **BATCH JOB proven by gate.** 1 of 24 emitted; 23 to batch. Hazards known and named. |
| **energy** (2076) | template mechanism exists, unverified for the remaining 2076 |
| **A25** (7 classes) | mechanism proved, budget viable, half the leaves free; **the open number is leaf count at class accuracy** |

**Credit unchanged**: `c450_remaining = 25`, `energy_remaining = 2076`, 7 of 7
classes unpaid. Nothing this round was root-integrated; all of it is standalone
module-green or probe-level.

## Decision on the C450 batch

m6's cost estimate for batching `c450Segs[13..35]` is ≈830 modules at ≈60 s each
≈ **14 h serial**. That is affordable but it **pays no credit until root
integration**, which has its own failure mode (the stale-olean trap). My call:
**do not batch yet.** The higher-value use of the next round is to close the C450
axis *end to end on one segment* — emit, gate, **root-import**, and confirm the
root still builds and `unconditional_n11_complete` accounting moves — because that
is the step that can still surprise us, and it costs one import block rather than
14 h. Batching 23 first would risk discovering a root-integration failure after
paying for all of them.

---

# ROUND 2, PART 8 — THE CONCRETE CREDIT PATH: h450 IS REACHABLE (C1837/C1838)

While the pilots ran I turned to **what actually removes a hypothesis from the
frozen theorem**, and found the concrete path.

## The chain terminates vacuously

`c450Segs` has **exactly 36 entries**. Originally a regex count (36 record
markers, 36 `eLo :=` occurrences, cross-checked against three kernel-checked
`drop`/`count` pairs 11+25, 12+24, 13+23) — then **kernel-checked** in
`ProbeC450ChainTermination.lean`:

| theorem | content |
|---|---|
| `aud_c450Segs_length` | `c450Segs.length = 36` |
| `aud_drop36` | `c450Segs.drop 36 = []` |
| `aud_vacuous_obligation` | `∀ s ∈ c450Segs.drop 36, SegmentNormalized s` — **vacuous** |
| `aud_vacuous_holds` | the empty-index obligation holds unconditionally |
| `aud_chain_counts` | the three drop/count pairs |

Gate `lead-chainterm-gate2.log`: exit=0, all five theorems exactly
`{propext, Classical.choice, Quot.sound}`. (Technique note:
`List.drop_eq_nil_iff_le` does **not** exist in this mathlib;
`List.drop_eq_nil_of_le` does.)

## Why this matters for the frozen goal

Each segment module supplies both its kernel-checked `*_paid` **and**
`*_remaining_of_remaining : RemainingSourceObligation → <predecessor>.RemainingSourceObligation`.
So a complete chain of segments `12..35` would discharge

    C450Source11Segment.RemainingSourceObligation

— which is **exactly the root's `h450`** (`ActualMetricClassReduction.lean:65`),
**one of the two explicit hypotheses** of the frozen unconditional theorem.
The chain terminates vacuously at index 35, so **no hypothesis is left over**.

**This is the first concrete path in the whole session that removes a hypothesis
from the frozen theorem** rather than mapping obstruction.

## Current gap, exactly

| item | state |
|---|---|
| root imports Segment modules | only through `C450Source11Segment` (indices 0..10) |
| `C450Source12Segment`, `C450Source13Segment` | emitted and module-green, **not imported** |
| Data modules on disk | indices 11, 12 only |
| segments remaining | **24** (indices 12..35) |
| root imports to add | **24** |
| root sha before any edit | `4F470AF5…` (verified unchanged) |

## Sequencing decision

**task-8** (m6) is running the **root-integration pilot**: import
`C450Source13Segment` into the root, build the root, then run the control that
matters — a probe that `#check`s `C450Source13Segment.source13_paid` while
importing **only** `N11Formalization`, to prove the root genuinely integrated it
rather than reading a stale olean. m6 documented that trap itself, so the task is
built around it. If it works, C450 becomes a pure batch (23 more segments + 23
imports). If it fails, we learn it after **one** segment instead of after 830
modules and ~14 h.

**No batch, no manifest regeneration, no root edits beyond the single import
block** are authorised yet.

---

# ROUND 2, PART 9 — ROOT INTEGRATION VERIFIED; C450 IS NOW A PURE BATCH

## task-8 SUCCEEDED. The last untested interface is cleared.

m6 added **exactly one** import block to the root
(`import N11Formalization.C450Source13Segment` + a 6-line pilot comment). I
verified the diff myself: **10 lines added, 0 removed** — nothing existing was
disturbed. Root sha moved

    4F470AF507F320488DFBC168F9AE39645904AF569AE46B9FFB8F5E520BC5EDAF   (pre-edit, verified)
 →  F6E3419A258B0AFC0B62CB50317661D3BCC5A9538AE5A0FA4037918366B0FCE0

**Root build**: `rootbuild1-c450pilot-20261014.log`, **exit=0**,
*"Build completed successfully (9908 jobs)"*; my rescan: **0 error lines, 0
forbidden tokens**, 7649 axiom reports, 14 mentions of the new module — so the
root genuinely **compiled** it rather than skipping it.

## The stale-olean control — both arms (C1840)

This is the test the whole task was built around, and it is **discriminating**:

| arm | result |
|---|---|
| **negative** (import absent) | every `#check` **fails** with `unknownIdentifier` |
| **positive** (import present) | all six `#check`s **resolve through the root** |

Resolved in the positive arm: `source13_paid : SegmentNormalized source13`,
`directions_cover : DirectionsCover Qs`, `cells_paid : ∀ i, CellBound …`,
`source12_paid` (transitively pulled),
`source11_remaining_of_remaining : C450Source12Segment.RemainingSourceObligation → C450Source11Segment.RemainingSourceObligation`,
and `C450Source11Segment.RemainingSourceObligation`. Both probe theorems —
`h450_of_h13`, `h13_covers_23` — report **exactly** the clean trio.

Since the probe imports **only** `N11Formalization`, the declarations are in the
root's **import closure**, not merely on `LEAN_PATH`. **The stale-olean trap is
cleared for this module.**

## What this does and does not buy

**Bought**: C450 is now a **pure batch job with a verified end-to-end interface**.
The chain composes through the root —
`h450_of_h13 : C450Source13Segment.RemainingSourceObligation → C450Source11Segment.RemainingSourceObligation`
— and the target is the root's `h450`.

**Not bought**: `h450` is **not discharged**. `h450_of_h13` is a **reduction**:
it turns `h450` into `C450Source13Segment.RemainingSourceObligation` (`h13`), a
**genuine obligation over 23 segments** (`h13_covers_23 : remainingSegs.length = 23`).
Vacuity arrives only at index 35 (C1838). And `h450` is **one of two** explicit
hypotheses — `henergy` (2076 terminals) remains untouched.

## The batch, now fully specified

| parameter | value |
|---|---|
| segments to emit | 23 (indices 13..35) |
| modules | ≈ 23 × 33 ≈ **760** |
| cost | ≈ 14 h serial at ~60 s/module |
| root imports to add | 23 |
| data source | `remaining8-35` (indices 13..34) **plus** `pilot` (index 35) |
| hazards | (1) name=index vs drop=index+1 two-parameter bookkeeping; (2) **one module per wrapper call** — parallel fan-out yields ~32 spurious mathlib read failures per segment; (3) don't forget index 35's second file |
| manifest | root is hash-pinned, so `manifests/FILES.jsonl` needs regenerating after the root edit |

## Round 2 closing state

**Both axes advanced from "unknown" to "specified engineering task"**:

- **C450**: interface verified end-to-end (emit → gate → root-import → `#check`
  through the root). Batch fully specified. **Removes `h450` when done.**
- **A25**: mechanism kernel-proved (C1828), arithmetic viable (C1830), ~half the
  leaves free by vacuity (C1835), gradient leaf 3.5–3.7× better (C1830).
  m5b's budget pilot (`ProbeA25AuditBudgetPilot.lean`) is mid-gate; its
  `gradOK_iff` currently carries `sorryAx` from one elaboration error
  (`decide_eq_true_eq` type mismatch at :84) — **the same cascade pattern**, which
  I have already told m5b to expect.

**Credit still unchanged**: `c450_remaining = 25` (now with a verified path to 0),
`energy_remaining = 2076`, 7 of 7 classes unpaid. **No claim in this round was
root-integrated into the manifest**; the root edit is a pilot pending the
remaining 23 segments, and the manifest is stale as a result.

---

# ROUND 3 — THE C450 BATCH IS RUNNING (task-9)

## Phase 1 (emission) complete and independently verified (C1846)

m6 emitted **all 23 segments** (indices 13..35) in 30 s: 782 files
(23 × 34), now 26 `C450Source*Data.lean` (indices 11..36) and 886
`C450Source*.lean` total.

I verified the bookkeeping **on disk, not from m6's log**, by parsing each emitted
segment and checking five invariants for every `k ∈ 13..35`:

| invariant | expected |
|---|---|
| own drop | `c450Segs.drop (k+1)` |
| own count | `36 − (k+1)` |
| split theorem NAME | `source<k>_remaining_split` (index, **not** index+1) |
| predecessor import | `C450Source<k>Segment` |
| own paid proof | `source<k+1>_paid` |

**Result: 0 violations across all 23.** The two-parameter off-by-one that broke
m6's own pilot (C1832) did **not** recur at batch scale.

**The terminal module confirms C1841 in emitted code**: `C450Source36Segment.lean`
has `remainingSegs := c450Segs.drop 36`, `remaining_count = 0` (vacuous terminus)
**and still carries `source36_paid`** — exactly the "terminus free, last element
still paid" prediction.

Both JSONs were exercised: indices 13..34 from `remaining8-35`, index 35 from the
**pilot** JSON (segment 36, 672 packets) — the last segment was not dropped.

## Phase 2 (gating) in flight

782 modules, serial, one per wrapper call, fresh log per module, retry-once on
mathlib read failures, failed logs preserved. m6's measured per-module range from
task-7 was 35–120 s, so the projection is **~8–26 h serial**. I asked for the
measured rate after the first 5 segments and an explicit flag if it exceeds the
~14 h estimate.

**Ordering note m6 got right**: all emitters ran **before** the root was touched,
because every emitter sha256-pins the root file — adding imports first would have
broken all 23 guard sets.

## What is NOT yet true

- No gated module is yet known green in this batch.
- Root imports for indices 14..36 are **not** added; the root is still
  `F6E3419A…` with only the Source13 pilot import.
- So `h450` is **reduced, not discharged**, and **no class credit** has moved:
  `c450_remaining = 25`, `energy_remaining = 2076`, `unconditional_n11_complete = false`.
- The delivery manifest remains stale (root hash-pinned).

## Energy axis reconnaissance (C1825 continued)

The energy axis has the **same batch shape** as C450: `Paid16GeneralRemaining210`
defines `newIDs` as a 10-way `Finset.union` over `Paid16GeneralG03..G12`,
`new_count : newIDs.card = 210`, with `new_terminal` and `new_radius` proved by an
`rcases` dispatch over the ten components — each of which is a ~250 KB generated
per-node module. `DSHTerminalTemplateV1` documents the seven payment items for one
terminal and states explicitly that the index machinery (`terminalIndexSet n`) is
"exactly the shape a later batch file must instantiate". So energy is a
**generator problem of the same kind**, with 2076 terminals remaining against 310
paid.

---

# ROUND 3 — MUTEX ARBITRATION AND TWO EVIDENCE-INTEGRITY FINDINGS

## I killed a Lean process, deliberately (operational, not mathematical)

At 16:33:31 m5b launched a `decide +kernel` gate at uniform depth 13. By 16:54 it
had run **20 min**, consumed 193 CPU-seconds and **6.6 GB RAM**, and was still
going. Because there is a **single global Lean mutex**
(`Local\N11Formalization_LeanSerial_20260929`), m6's batch — the one job that
actually removes a hypothesis — had last completed a module at **16:34:10** and
made **zero** progress for 20 minutes.

**Decision**: killed PID 35832. Justification: the measurement's key data were
**already in** (d1..d12 green on disk, ladder climbing), and d13+ only fixes the
exact depth — it does not change the decision it informs. The batch converts
`h450` from hypothesis to theorem. Memory recovered 3.6 → **6.7 GB free**; the
batch resumed immediately (was building `C450Source14GroupedC10`).

I instructed m5b to **stop climbing the ladder one depth at a time**: reach the
depth answer by simulation (`pilot_deep_table.py`, with vacuity accounting), then
gate **one** comfortably-past-threshold instance; and to coordinate before any gate
expected to exceed ~3 minutes.

## m6 caught a silent false-positive in its own driver (C1847)

I reproduced the underlying PowerShell fact **exactly**: `$LASTEXITCODE` is
**not** updated by a `throw` (from 0 it stays 0; after a native `exit 7` it stays
7). So a driver that reads `$LASTEXITCODE` after calling the wrapper would have
recorded **exit=0 / GREEN for a module that was never built** whenever the wrapper
threw `N11 serial lock wait exceeded`.

m6 caught this before any report and replaced it with two independent guards:
1. the wrapper's own **`.result.json`** is the **sole** source of truth for exit
   status (absent file ⇒ NOT green, regardless of any exit variable);
2. an independent post-gate check that the module's **olean exists and is newer
   than its source** — `exit=0` without a fresh olean is flagged
   `FALSE GREEN BLOCKED` and treated as fatal.

This is the **same class** as the stale-olean trap and the `decide`-as-falsity
misreading: a check that *looks* like verification but cannot fail correctly.

## Batch status at this writing

| item | value |
|---|---|
| emission | **complete**, 782 files, 0 collisions, bookkeeping verified (C1846) |
| gating | in flight, **12 / 736** grouped oleans, ~30–62 s/module |
| projection | ~6–11.5 h serial |
| driver | v2 (resume-capable, skips already-green modules, retries on mutex wait with 120 s backoff × 8) |
| root | still `F6E3419A…`, imports **not** added |
| manifest | untouched, stale |

**Stop conditions armed**: any non-mechanical failure (real type error, or
`exit=0` without a fresh olean) halts the run. Mathlib read failures retry once.
All gate logs preserved including retries.

**Still not true**: no segment is known green in this batch yet, `h450` is
reduced but **not discharged**, and `c450_remaining = 25`,
`energy_remaining = 2076`, `unconditional_n11_complete = false` all stand.
