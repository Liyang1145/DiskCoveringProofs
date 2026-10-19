# A25 — CANONICAL FINITE CERTIFICATES — HANDOFF (2026-10-13)

**Accepted checkpoint:** `ACCEPTANCE-A25-CANONICAL-FINITE-CERTIFICATES-20261013.json`
**Root SHA256:** `4F470AF507F320488DFBC168F9AE39645904AF569AE46B9FFB8F5E520BC5EDAF`
**233/233 framework modules green. 30 new modules. `unconditional_n11_complete = false`.**

This supersedes nothing: A24 (`ACCEPTANCE-A24-ACTIVE-INTERVAL-CERTIFICATES-20261008.json`,
203 modules, root `16EA5086...A1F6`) remains the prior accepted checkpoint and its
sources and probe evidence are byte-unchanged (verified: 203/203 module hashes and
both A24 probe logs/sources hash-match).

---

## 1. WHAT A25 IS, AND WHAT IT IS NOT

A25 earns **FRAMEWORK CREDIT ONLY**. **No class exclusion, no C450 segment and no
energy terminal is newly paid.** The frozen objective is unchanged:

```lean
∀ (r : ℝ) (c : Fin 11 → Point),
  0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r
```

Unchanged historical counts (asserted, not merely reported):

| quantity | value |
|---|---|
| `c450_remaining` | **25** |
| `energy_remaining` | **2076** |
| `sharp_paid` | **120** |
| `unconditional_n11_complete` | **false** |
| class exclusions remaining | **7** |

The three obligations still carried explicitly into the accepted consumer are
`C450Source11Segment.RemainingSourceObligation`,
`EnergyTerminalBatchB11.RemainingTerminalRadius`,
`ActualMainRoute.Canonical33Obligation`.

---

## 2. WHAT WAS ACTUALLY GAINED (structural, not count-based)

* **Canonical rational coordinates.** `ActualCanonicalFaceCoordinates.q0Coordinates` /
  `q1Coordinates`, `ActualCanonicalMomentTransport.constantCoeffQ_pullback` /
  `maskBalanced_pullback` — actual face/slot/edge coordinate builders and exact
  rational coefficient/mask/constant transport.
* **Finite rational tables replace real-valued bounds.**
  `CanonicalSharedMomentFiniteCertificate.FiniteCanonicalCertificate` carries only
  finite rational tables (`faceMax`, `switchMax`, `sectorMax`) plus
  `EfficientFaceCertificate` / `SwitchCertificate` / `EfficientSectorCertificate`
  leaves and a strict rational total; `toCanonical` converts it into a real
  `CanonicalCertificate`, producing the semantic bounds internally.
* **The full-disk quantifier theorem, with the unpaid hypotheses still explicit.**
  `seven_class_exclusions_of_finite` consumes `SevenFiniteTables` (the 7 unpaid
  class tables: q0 degrees 3/4/5, q1 degrees 3/4/5, q1 balanced), and
  `full_disk_bound_of_finite_class_tables` then yields the full-disk statement for
  arbitrary `Fin 11` covers **with `h450` and `henergy` still explicit**. This is a
  genuine reduction of the reduction surface — the classes are now consumed as
  finite tables — but it does **not** pay them.
* **8 → 2 reduction for the q1-balanced class.**
  `CanonicalSharedMomentOrbitTransport.balanced_certificates_of_two` produces a
  certificate for all 8 cuts of the q1-balanced class from TWO representative
  certificates. `CanonicalBalancedGraphOrbits.balanced_orbit` is the orbit
  structure behind it.
* **`CanonicalBalancedFiniteClassCertificate.balanced_exclusion_of_two_finite` +
  `SixAndBalancedFiniteTables`** — Q1RunExclusion 4 from 2 representative finite
  tables.

### 2a. The honest negative result: nine proved leaf certificates, no consumer satisfied

This must not be read as progress toward class credit. For
`SharedMomentConcreteSwitchBatch` (m2's analysis, relayed here as found, not as
re-verified by the acceptance pipeline):

* **G1 — no aggregation theorem.** `start0_switch_total_bound := 22523/250000` is
  defined and referenced by **nothing**. The batch proves all nine
  `start0_switch{i}_full_angle_upper` theorems (7923 node theorems, 9/9 terminate,
  no gaps) but there is no theorem that assembles them into a bound.
* **G2 — the consumer demands a different structure.**
  `FiniteCanonicalCertificate.switches` requires
  `SwitchCertificate (canonicalSwitchP D kap i) ...`, a structure over
  `GradientSwitchLeaf`. The batch does not produce it, and **no coefficient-identity
  proof** ties the batch's `p/q/b/d2/d1` to `canonicalSwitch*` of any instantiated
  `CanonicalCoeffQ F`. So the nine leaf-level certificates satisfy no consumer.
* **G4 — namespace hazard.** `start0_switch0_bound` is `1/2000` in
  `SharedMomentConcreteLeafControls.lean` (lines 34-39) but `141/1000000` in
  `SharedMomentConcreteSwitchBatch.lean` (lines 12-17). The names are legal and
  distinct (different namespaces), but a future bridge that opens both would
  silently take the wrong value. **Record this before writing any bridge.**

Also, from the A25 diagnostic record
(`a25-face1-direct-diagnostic-failure.json`): direct whole-cell interval
arithmetic for the `start0_face1` tree blew the 250000-node diagnostic budget, so
local gradient certification was required. **Concrete class costs are not routine
table filling — instance count matters far more than one more bound.**

---

## 3. THE ACCEPTED ARTIFACTS

| artifact | path |
|---|---|
| acceptance | `evidence\codex-handoff\ACCEPTANCE-A25-CANONICAL-FINITE-CERTIFICATES-20261013.json` |
| manifest | `evidence\codex-handoff\a25-canonical-finite-certificates-20261013-manifest.json` (233/233, `incomplete_modules` empty) |
| root pair | `evidence\resume-lead\root-a25-canonical-finite-certificates-20261013-pair.json` |
| root audit probe log | `evidence\codex-handoff\a25-canonical-finite-root-audit-20261013-gate2.log` |
| control probe log | `evidence\codex-handoff\a25-canonical-finite-controls-20261013-gate2.log` |
| consistency report | `evidence\codex-handoff\a25-final-readonly-consistency-20261013.json` |
| driver | `evidence\codex-handoff\Invoke-A25CanonicalFiniteAcceptance-20261013.ps1` |
| staging tool | `evidence\codex-handoff\Stage-A25ModuleEvidence-20261013.ps1` |
| readiness guard | `evidence\codex-handoff\Check-A25ManifestReadiness-20261013.ps1` |
| consistency script | `evidence\codex-handoff\Verify-A25Consistency-20261013.ps1` |
| Phase-1 report | `evidence\a25-landing-20261013\m4\PHASE1-REPORT.md` |

### 3a. Frozen root runs

```
run1: exit=0 unchanged=True source_count=1521 changed_sources=0 modules=976  16:27:34 → 16:28:59
run2: exit=0 unchanged=True source_count=1521 changed_sources=0 modules=975  16:28:59 → 16:29:16
root_sha256_before == root_sha256_after == 4F470AF5...EDAF on BOTH runs
```

`source_count` 1521 ≥ the `MinimumSources` floor 1513.

**Cost note — 67 s is NOT a general figure.** run1 took **67 s**
(`Built N11Formalization (67s)`, 9841 jobs) and run2 **17 s**, but *only because
all 30 new modules already had oleans* built by m1/m2/m3, so run1 merely rebuilt
the root itself and replayed the rest. **A cold run of this 788-import root on a
fresh machine would be substantially longer** — do not budget from this number.
(The mutex wait should still be generous: the historical default of 600 s was
raised to 5400 s precisely because a single peer module build can exceed 10 min —
`SharedMomentConcreteSwitchBatch` took 1042 s. Use
`Invoke-LeanSerial20261013.ps1`, which defaults to 5400 s.)

### 3b. Probe evidence

* Audit probe `ProbeA25CanonicalFiniteRootAudit.lean`
  (SHA256 `9D56E891...C96`): exit 0, `unchanged`, **174** `depends on axioms:`
  reports, **0** unpermitted axioms, **0** matches of
  `sorryAx|native_decide|Lean.ofReduceBool|error[:(]`, and **all 30** required
  needles present.
* Control probe `ProbeA25CanonicalFiniteControls.lean`
  (SHA256 `9DB9E909...D37`): exit 0, `unchanged`, **14** axiom reports, **0**
  unpermitted, and all **8** required control needles present.
* Allowed axioms everywhere: exactly `propext`, `Classical.choice`, `Quot.sound`.

---

## 4. FIVE LANDMINES FOUND AND DEFUSED (read before touching A25)

1. **The driver declared 28 extras, not 30.** The 2026-10-08 driver omitted
   `CanonicalBalancedFiniteClassCertificate` and
   `SharedMomentConcreteSectorGradientControls`. Corrected to 30 → total 233.
2. **`sourceRoot 6` is a load-bearing needle with zero direct occurrences.**
   `Accept-A9Framework-20261005.ps1` demands the literal substring `sourceRoot 6`
   in the audit log. `ProbeA25CanonicalFiniteRootAudit.lean` contains **453**
   occurrences of `sourceRadius` and **zero** of `sourceRoot`; the string is emitted
   only because **line 101** `#print N11Formalization.SourceExactRoot.sourceRadius`
   prints the definition body as two lines, the second being exactly
   `N11Formalization.SourceExactRoot.sourceRoot 6`. **Do not delete line 101** —
   it looks redundant and removing it breaks acceptance with
   `Missing actual root consumer/interface sourceRoot 6`. (Empirically confirmed,
   byte-verified, in `m4\needle-calibration-gate1.log`.)
3. **The manifest's evidence discovery is non-recursive and single-directory.**
   `Invoke-A21Manifest-20261007.ps1` line 18 uses
   `Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.log.result.json' -File`, so
   evidence under `evidence\a25-landing-20261013\mN\` is **invisible** and a green
   module is scored red. Fixed by `Stage-A25ModuleEvidence-20261013.ps1`
   (restages into `codex-handoff`, rewriting only the JSON's `log` field; the
   shared manifest and acceptance scripts stay byte-identical).
4. **Rule-3 regression hazard when staging.** The manifest independently picks the
   newest gate and the newest build, requiring `build.started >= gate.started`.
   Naively staging a *fresh* gate without a correspondingly fresh build therefore
   flips a **green** module to **red**. This fired for real on
   `SharedMomentA25CertificateControls` (fresh gate 14:14 vs older build 13:59).
   Staging is now pair-aware and refuses to introduce a regression, and also
   re-checks rule 5 on the staged gate log before accepting it.
5. **The stale-olean trap.** `lake env lean Probe....lean` does **not** rebuild
   imported modules: `import N11Formalization` resolves against the existing
   `N11Formalization.olean`. Immediately after the 30 root imports landed, that
   olean was still the A24-era artifact (olean mtime `2026-10-08 13:48:49` vs root
   source `2026-10-13 15:52:42`), so the probe was elaborated against a root with
   no A25 modules and 37 `unknown identifier` errors on lines 451-487.
   **Correct order: ROOT PAIR FIRST (it rebuilds the root olean), THEN the probe
   gates.** On an unchanged probe file the result went exit 1 → exit 0 after the
   root pair. `gate1` is kept as append-only evidence of this failure and is
   **not** referenced by the driver.

### 4a. `-ControlLog` needs BOTH control families

`Accept-A9Framework-20261005.ps1` line 60 **hard-codes** three A20 incident
needles (`crossing_diagonals_true_common_nearest`, `no_diagonal_positive_facet`,
`large_empty_arc_support`) for `-ControlLog`, while the A25 consistency check
requires five different A25 needles. No pre-existing log carries all eight, so
`lean\ProbeA25CanonicalFiniteControls.lean` was written to establish **both**
families in one log: the three A20 statements are **re-proved there** (real kernel
axiom reports in that file), and the eleven `SharedMomentA25CertificateControls`
statements are reported via `#print axioms`. That probe is the `-ControlLog`
source. Do not point `-ControlLog` at a log carrying only one family.

### 4b. `SharedMomentA25CertificateControls` defect (fixed)

The module had never compiled: `simp [chordSq] at hp` left a residual that `simp`
did not close, and two theorems carried `sorryAx`. Fix = exactly one added line
`exact absurd hp (by norm_num)` (line 64); **both theorem statements unchanged**.
Correction to the original diagnosis: the residual was
`hp : 2 * ![0,1,1] 2 < 1 + ![0,1,1] 2 ^ 2` — one normalization level *earlier*
than the briefing stated — and `norm_num [chordSq] at hp` alone does **not** close
it. Do not re-try that repair.

---

## 5. REPRODUCTION

```powershell
$h='E:\ai4math2\research-2026\n11-formalization\evidence\codex-handoff'
$rl='E:\ai4math2\research-2026\n11-formalization\evidence\resume-lead'

# 1. root pair FIRST (rebuilds the root olean; required before the probes)
& "$rl\Invoke-RootPair.ps1" -Tag a25-canonical-finite-certificates-20261013

# 2. audit probe gate (fresh suffix)
& "$rl\Invoke-LeanSerial20261013.ps1" -File 'ProbeA25CanonicalFiniteRootAudit.lean' `
  -Log "$h\a25-canonical-finite-root-audit-20261013-gate2.log"

# 3. control probe gate (fresh suffix)
& "$rl\Invoke-LeanSerial20261013.ps1" -File 'ProbeA25CanonicalFiniteControls.lean' `
  -Log "$h\a25-canonical-finite-controls-20261013-gate2.log"

# 4. staging -> guard -> manifest -> post-check -> acceptance
& "$h\Invoke-A25CanonicalFiniteAcceptance-20261013.ps1"

# 5. consistency
& "$h\Verify-A25Consistency-20261013.ps1"
```

All Lean/Lake invocations go through a serial wrapper (single global mutex
`Local\N11Formalization_LeanSerial_20260929`); **never** run Lean with cwd under
`C:` — that tree is stale (see `BRIEFING.md` §0). Evidence is append-only: use a
fresh suffix, never overwrite a log or JSON.

---

## 6. WHAT IS STILL UNPAID

* **All 7 Q0/Q1 class exclusions.** A25 consumes them as finite tables
  (`SevenFiniteTables`) but does not pay them.
* **25 C450 source segments; 2076 energy terminals** (389 without genuine routes).
* **The unconditional SAME `sourceRoot 6` arbitrary-cover theorem.**
* **Representative finite tables** for the two-table balanced class certificate and
  the 8→2 balanced orbit transport.
* **The SwitchBatch bridge** — G1 (no aggregation theorem) and G2 (no
  coefficient-identity proof to `canonicalSwitch*`) both remain open.
* **Consumer-satisfying concrete factor certificates**: no class is paid before
  complete coefficient/mask tables, every factor certificate, and a strict total
  are instantiated and kernel-checked. HOST complete tree plans and exact total
  budgets are **not** Lean evidence.

---

## 7. NEXT EXECUTABLE STEP

Attack the two concrete blockers that currently make the largest finite artifacts
worthless: (1) prove an **aggregation theorem** for the nine
`start0_switch{i}_full_angle_upper` leaves in `SharedMomentConcreteSwitchBatch`,
consuming `start0_switch_total_bound`; and (2) prove the **coefficient-identity**
lemma tying that batch's `p/q/b/d2/d1` to `canonicalSwitch*` of an instantiated
`CanonicalCoeffQ F`, so that `FiniteCanonicalCertificate.switches` can actually be
satisfied. Guard against the G4 namespace collision (`start0_switch0_bound` is
`1/2000` in LeafControls vs `141/1000000` in SwitchBatch) when writing that bridge.
