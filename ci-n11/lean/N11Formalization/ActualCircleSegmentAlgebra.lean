import N11Formalization.ActualBoundarySwitchAngles
import N11Formalization.ActualRingShoelacePositive

/-! Exact circular-segment algebra for genuine owned widths.
This is only the trigonometric bookkeeping layer; it does not assert
that the clipped-cell straight pieces have the corresponding area sum. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCircleSegmentAlgebra
open FlashTiling

def segmentTerm (w : ℝ) : ℝ := (w-Real.sin w)/2

theorem segmentTerm_add (a b : ℝ) :
    segmentTerm a+segmentTerm b=(a+b-(Real.sin a+Real.sin b))/2 := by
  unfold segmentTerm
  ring

theorem segmentTerm_sum_widths {n : ℕ} (w : Fin n → ℝ)
    (hsum : ∑ i, w i=2*Real.pi) :
    ∑ i, segmentTerm (w i) =
      Real.pi-(∑ i, Real.sin (w i))/2 := by
  unfold segmentTerm
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul,Finset.sum_sub_distrib,hsum]
  ring

theorem segmentTerm_nonneg {w : ℝ} (hw0 : 0 ≤ w) (hwpi : w ≤ 2*Real.pi) :
    0 ≤ segmentTerm w := by
  unfold segmentTerm
  have hs := Real.sin_le hw0
  linarith

theorem circleMap_det_segment (a b : ℝ) :
    det2 (circleMap a) (circleMap b)=Real.sin (b-a) :=
  ActualRingShoelacePositive.det_circleMap a b

theorem switchAtom_is_chord_offset {a b U : Point} {r : ℝ}
    (S : ActualBoundarySwitchMetric.SwitchData a b U r) :
    S.radius^2*Real.sin (2*ActualBoundarySwitchAngles.SwitchData.angle S)/2 =
      S.chord*S.offset :=
  ActualBoundarySwitchAngles.SwitchData.exact_area_atom S

end N11Formalization.ActualCircleSegmentAlgebra
#check @N11Formalization.ActualCircleSegmentAlgebra.segmentTerm_sum_widths
#check @N11Formalization.ActualCircleSegmentAlgebra.segmentTerm_nonneg
#print axioms N11Formalization.ActualCircleSegmentAlgebra.segmentTerm_sum_widths
#print axioms N11Formalization.ActualCircleSegmentAlgebra.switchAtom_is_chord_offset
