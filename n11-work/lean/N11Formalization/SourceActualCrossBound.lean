import N11Formalization.SourceCrossPacket
import N11Formalization.SourceRelativeFluxNorms

/-! True raw8->canonical6 pinned Cmat Frobenius and operator bounds for ALL
pinned x,z. No membership/norm/operator premise, no global9 bound inferred. -/
set_option autoImplicit false
namespace N11Formalization.SourceActualCrossBound
open N11Formalization RatInterval ResumeLocalIncidence ResumePinnedMatrixReindex
open SourceResponseFluxIdentity SourceCrossGeometry SourceCrossPacket
noncomputable section

def canonicalCrossBox (i j : Fin 8) : RatInterval := CB (pinEquiv i) (pinEquiv j)

theorem canonicalCrossBox_mem (i j : Fin 8) :
    (canonicalCrossBox i j).Mem (FlashLocal.Cmat sourceResponse sourceAngle
      ((6 : Fin 9).succAbove i) ((6 : Fin 9).succAbove j)) := by
  have h := CB_mem (pinEquiv i) (pinEquiv j)
  simp only [rawCross,SourceRelativeFluxNorms.pin_source] at h
  exact h

theorem canonical_frobenius_certificate :
    (∑ i : Fin 8,∑ j : Fin 8,(canonicalCrossBox i j).abs.hi^2)≤(179/5000 : ℚ)^2 := by
  have hj (i : Fin 8) :
      (∑ j : Fin 8,(CB (pinEquiv i) (pinEquiv j)).abs.hi^2)=
        ∑ j : Fin 8,(CB (pinEquiv i) j).abs.hi^2 :=
    pinEquiv.sum_comp (fun j => (CB (pinEquiv i) j).abs.hi^2)
  change (∑ i : Fin 8,∑ j : Fin 8,(CB (pinEquiv i) (pinEquiv j)).abs.hi^2)≤_
  simp_rw [hj]
  rw [pinEquiv.sum_comp (fun i => ∑ j : Fin 8,(CB i j).abs.hi^2)]
  exact frobenius_certificate

/-- Actual Cmat restricted to canonical6, not an assumed full9 operator bound. -/
theorem actual_pinned_frobenius :
    (∑ i : Fin 9,∑ j : Fin 9,
      (if i=6 ∨ j=6 then 0 else FlashLocal.Cmat sourceResponse sourceAngle i j)^2)≤
        (179/5000 : ℝ)^2 :=
  FlashLocal.hCfrob_of_boxes 6 sourceResponse sourceAngle canonicalCrossBox
    canonicalCrossBox_mem canonical_frobenius_certificate

theorem actual_pinned_operator (x z : Fin 9 → ℝ) (hx : x 6=0) (hz : z 6=0) :
    |∑ i : Fin 9,∑ j : Fin 9,FlashLocal.Cmat sourceResponse sourceAngle i j*x i*z j|≤
      (179/5000 : ℝ)*Real.sqrt (∑ i : Fin 9,x i^2)*Real.sqrt (∑ j : Fin 9,z j^2) :=
  FlashLocal.pinned_operator_le_of_frobenius 6
    (FlashLocal.Cmat sourceResponse sourceAngle) (by norm_num)
    actual_pinned_frobenius x z hx hz

end
end N11Formalization.SourceActualCrossBound
#check @N11Formalization.SourceActualCrossBound.actual_pinned_frobenius
#check @N11Formalization.SourceActualCrossBound.actual_pinned_operator
#print axioms N11Formalization.SourceActualCrossBound.actual_pinned_operator
