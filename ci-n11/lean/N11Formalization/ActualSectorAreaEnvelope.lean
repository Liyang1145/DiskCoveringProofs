import N11Formalization.ActualSharedFactorArea

/-! Correct closed-domain envelope for unequal ownership endpoint radii.
The max with 1/2 retains skew endpoints when the sector angle is small.
No equal-radius or saturated-radius hypothesis is introduced. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSectorAreaEnvelope

open ActualCoverStructuralReduction ActualBoundaryNineTies
open ActualMetricAngleAtoms ActualSectorMetricDomain ActualSharedFactorArea
open ActualOwnershipSwitchWidths ActualCircleSegmentAlgebra

def widthEnvelope (α : ℝ) : ℝ :=
  2*Real.arcsin ((19/50 : ℝ)*max (1/2) (Real.sin (α/2)))

def areaEnvelope (α : ℝ) : ℝ :=
  (19/50 : ℝ)^2*Real.sin α/2 + segmentTerm (widthEnvelope α)

theorem quadratic_box_envelope {u v z : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    u^2+v^2-2*u*v*z ≤ max 1 (2-2*z) := by
  have huq : u^2 ≤ u := by nlinarith
  have hvq : v^2 ≤ v := by nlinarith
  have huv : 0 ≤ u*v := mul_nonneg hu0 hv0
  have hcoef : 0 ≤ u+v-2*u*v := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hv1),
      mul_nonneg hv0 (sub_nonneg.mpr hu1)]
  have hsum : u+v-u*v ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1)]
  let M := max (1 : ℝ) (2-2*z)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMz : 2-2*z ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := by linarith
  have hleft := mul_le_mul_of_nonneg_left hM1 hcoef
  have hright := mul_le_mul_of_nonneg_left hMz huv
  have hlast := mul_le_mul_of_nonneg_right hsum hM0
  dsimp [M] at *
  nlinarith only [huq,hvq,hleft,hright,hlast]

theorem half_sine_envelope {α : ℝ} (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi) :
    max (1 : ℝ) (2-2*Real.cos α) ≤
      (2*max (1/2 : ℝ) (Real.sin (α/2)))^2 := by
  have hs0 : 0 ≤ Real.sin (α/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have ht0 : (1/2 : ℝ) ≤ max (1/2 : ℝ) (Real.sin (α/2)) := le_max_left _ _
  have hts : Real.sin (α/2) ≤ max (1/2 : ℝ) (Real.sin (α/2)) := le_max_right _ _
  have hc : 2-2*Real.cos α = 4*Real.sin (α/2)^2 := by
    have hh := Real.cos_two_mul (α/2)
    have hsum := Real.sin_sq_add_cos_sq (α/2)
    rw [show 2*(α/2)=α by ring] at hh
    nlinarith
  apply max_le
  · nlinarith
  · rw [hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hts)
      (show 0 ≤ max (1/2 : ℝ) (Real.sin (α/2))+Real.sin (α/2) by linarith)]

theorem actual_sector_width_envelope {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchGap v i ≤ widthEnvelope (sectorAngle v i) := by
  have hd := actual_normalized_endpoint_domain h hr v i
  have hα := actual_sector_angle_bounds v i
  have hq := quadratic_box_envelope hd.1.le hd.2.1 hd.2.2.1.le hd.2.2.2
    (z := Real.cos (sectorAngle v i))
  change chordQuadratic v i ≤ _ at hq
  have hs : Real.sqrt (chordQuadratic v i) ≤
      2*max (1/2 : ℝ) (Real.sin (sectorAngle v i/2)) :=
    Real.sqrt_le_iff.mpr ⟨by positivity,
      hq.trans (half_sine_envelope hα.1 hα.2)⟩
  have ha := Real.arcsin_le_arcsin
    (show (19/50 : ℝ)*Real.sqrt (chordQuadratic v i)/2 ≤
        (19/50 : ℝ)*max (1/2 : ℝ) (Real.sin (sectorAngle v i/2)) by linarith)
  rw [actual_factor_width_formula h hr v i]
  unfold widthEnvelope
  linarith

theorem segmentTerm_monotone : Monotone segmentTerm := by
  intro a b hab
  have hs := Real.abs_sin_sub_sin_le b a
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hs
  have hh := (le_abs_self (Real.sin b-Real.sin a)).trans hs
  unfold segmentTerm
  linarith

theorem actual_sector_area_envelope {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    sectorArea v i ≤ areaEnvelope (sectorAngle v i) := by
  have hd := actual_normalized_endpoint_domain h hr v i
  have hα := actual_sector_angle_bounds v i
  have hs : 0 ≤ Real.sin (sectorAngle v i) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 hα.2
  have huv : leftNormalized v i*rightNormalized v i ≤ 1 := by
    nlinarith [mul_nonneg hd.1.le (sub_nonneg.mpr hd.2.2.2)]
  have htriangle := mul_nonneg (sub_nonneg.mpr huv) hs
  have hsegment := segmentTerm_monotone (actual_sector_width_envelope h hr v i)
  unfold sectorArea areaEnvelope
  nlinarith only [htriangle,hsegment]

theorem actual_total_width_envelope {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) :
    2*Real.pi ≤ ∑ i : Fin 9, widthEnvelope (sectorAngle v i) := by
  rw [← actual_switch_gap_sum v]
  exact Finset.sum_le_sum fun i _ => actual_sector_width_envelope h hr v i

theorem actual_total_sector_area_envelope {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) :
    (∑ i : Fin 9, sectorArea v i) ≤ ∑ i : Fin 9, areaEnvelope (sectorAngle v i) :=
  Finset.sum_le_sum fun i _ => actual_sector_area_envelope h hr v i

end N11Formalization.ActualSectorAreaEnvelope
#check @N11Formalization.ActualSectorAreaEnvelope.actual_sector_width_envelope
#check @N11Formalization.ActualSectorAreaEnvelope.actual_sector_area_envelope
#check @N11Formalization.ActualSectorAreaEnvelope.actual_total_width_envelope
#print axioms N11Formalization.ActualSectorAreaEnvelope.quadratic_box_envelope
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_sector_width_envelope
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_sector_area_envelope
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_total_width_envelope
#print axioms N11Formalization.ActualSectorAreaEnvelope.actual_total_sector_area_envelope
