/-
DSHPatchTemplateK5Fail.lean -- DSH-PATCH-T0 NEGATIVE-CONTROL FAILURE LOG (expected exit != 0).

Companion to `DSHPatchTemplateK5.lean` (positive, exit=0) and
`DSHPatchTemplateK5Probe.lean` (kernel-proved refutations of the same three bad variants,
exit=0).  This file imports the MAIN module only (the probe module's olean is standalone-only),
and restates the replaced-constant / wrong-orientation claims as if they were provable, using
the SAME closing tactics that work for the correct versions in the same file.

Each error below is the INTENDED MATHEMATICAL failure, not an elaborator accident, because the
aimed statements are provably false in `DSHPatchTemplateK5Probe.lean`:

  FAIL-1  replaced MIXED constant `Mbad = 71` (actual: `1468*((99/200)*(2/25)+429/50000) =
          884103/12500 = 70.72824`).  FALSE: NC-D
          (`K5Probe.separate_blocks_do_not_imply_mixed`; exact rationals q = 729/50000,
          p = 37732311/3670000000000, E = 1/500000000 gives mixed form 1.56918e-9 <= E = 2e-9
          while q^2/1e5 = 2.125764e-9 fails) and `K5Probe.Mbad_exceeds_critical_sq`
          (`71 > M_crit = 70.74488...`).  Contrast: `good_mixed_constant_claim` below, the SAME
          statement at the ACTUAL constant, is GREEN in this very file.

  FAIL-2  replaced CONTAINMENT radius `1459/100000` (frozen: `729/50000`).  FALSE: NC-B
          `K5Probe.enlarged_radius_rejected` proves `coefficient (1459/100000) < 1/100000`, so
          `(1/100000) q^2 <= coefficient q * q^2` fails at `q = 1459/100000`
          (`K5Probe.enlarged_radius_gain_fails`).  Contrast: `good_radius_claim` below, at the
          FROZEN radius, is GREEN.

  FAIL-3  FLIPPED hull rows (`k5hi` as lower, `k5lo` as upper).  FALSE: NC-A
          `K5Probe.flipped_endpoints_rejected` proves `not (memberOK k5hi k5lo db4935)`, with the
          right-reason witness `not (k5hi 0 <= -db4935 0 6)` (`-33/64 <= -267/512` is false).
          Contrast: the correct orientation is the root-imported `Patch120K5.member4957`-style
          `Patch120K5.member4935`.

Note (lead + patch-survey): a narrowed CELL matrix `d` is NOT usable as a failure control
(`Cell` is antitone in `d`); NC-C in the probe file is the hull-excludes-cell control instead.
-/
import N11Formalization.DSHPatchTemplateK5
import N11Formalization.Patch120K5

set_option autoImplicit false

namespace N11Formalization.DSHPatchTemplate.K5Fail

open Finset
open N11Formalization
open N11Formalization.Patch120K5
open N11Formalization.ResumeRelativeScalar

noncomputable section

/-- Probe-local copy of the replaced mixed coefficient used by `DSHPatchTemplateK5Probe`. -/
def Mbad : ℝ := 71

/-! ## GREEN contrast pair (both must pass, so the red lines are isolated to the constant) -/

/-- Correct-constant version: GREEN (same goal shape as FAIL-1, actual coefficient). -/
theorem good_mixed_constant_claim {q p : ℝ} (hq : 0 ≤ q) (hr : q ≤ 729 / 50000) :
    (1 / 100000 : ℝ) * q ^ 2
      ≤ (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
        - 1468 * ((99 / 200) * (2 / 25) + 429 / 50000) * p * q ^ 2 := by
  have hcomp := K5.mixed_remainder_completion q p
  have hc := K5.sharp_coefficient_gate hq hr
  have hmul : (1 / 100000 : ℝ) * q ^ 2 ≤ coefficient q * q ^ 2 :=
    mul_le_mul_of_nonneg_right hc.le (sq_nonneg q)
  have hs : 0 ≤ 734 * (p - ((99 / 200) * (2 / 25) + 429 / 50000) * q ^ 2) ^ 2 := by positivity
  linarith [hcomp, hmul, hs]

/-- Frozen-radius version: GREEN (same goal shape as FAIL-2, frozen radius). -/
theorem good_radius_claim :
    (1 / 100000 : ℝ) * (729 / 50000) ^ 2
      ≤ coefficient (729 / 50000) * (729 / 50000) ^ 2 := by
  have h := K5.sharp_coefficient_gate (by norm_num : (0 : ℝ) ≤ 729 / 50000) le_rfl
  exact mul_le_mul_of_nonneg_right h.le (by norm_num)

/-! ## RED claims (expected errors: intended mathematical falsity) -/

/-- FAIL-1 (expected error: tactic cannot close a false goal) -- replaced mixed constant. -/
theorem bad_mixed_constant_claim {q p : ℝ} (hq : 0 ≤ q) (hr : q ≤ 729 / 50000) :
    (1 / 100000 : ℝ) * q ^ 2
      ≤ (9 / 10000 : ℝ) * q ^ 2 + 734 * p ^ 2 - (179 / 5000) * q ^ 3 - ((2 / 25) / 3) * q ^ 4
        - Mbad * p * q ^ 2 := by
  have hcomp := K5.mixed_remainder_completion q p
  have hc := K5.sharp_coefficient_gate hq hr
  have hs : 0 ≤ 734 * (p - ((99 / 200) * (2 / 25) + 429 / 50000) * q ^ 2) ^ 2 := by positivity
  linarith [hcomp, hc, hs, sq_nonneg q]

/-- FAIL-2 (expected error: `norm_num` on a false closed inequality) -- replaced radius. -/
theorem bad_radius_claim :
    (1 / 100000 : ℝ) * (1459 / 100000) ^ 2
      ≤ coefficient (1459 / 100000) * (1459 / 100000) ^ 2 := by
  norm_num [coefficient]

/-- FAIL-3 (expected error: `decide` failed, the decided proposition is false) -- flipped rows. -/
theorem bad_hull_orientation_claim : memberOK k5hi k5lo db4935 := by
  unfold memberOK
  decide +kernel

end

end N11Formalization.DSHPatchTemplate.K5Fail