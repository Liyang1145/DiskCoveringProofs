import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NonconstantOuterControls
open C450OuterGeometry C450OuterCellMajorant

theorem actual_sixth_not_zero : C450SixthAnalytic.W0.a1 ≠ 0 :=
  C450SixthAnalytic.outer_not_constant
theorem wrong_sign_factor_rejected :
    ¬((-1:ℝ)*1*(-1) ≤ (-1:ℝ)*((3/4)*(-1))*1) := by norm_num
theorem correct_sign_factor :
    (-1:ℝ)*1*(-1) ≤ (-1:ℝ)*signedFactor (3/4) (-1)*1 :=
  signed_harmonic (by norm_num) (by norm_num) le_rfl (by norm_num) le_rfl
theorem missing_cubic_domain_rejected : ¬(P3 (0:ℝ) ≤ P3 (1/2)) := by
  norm_num [P3]
theorem inflated_capacity_rejected :
    C450SixthAnalytic.W0.a0+C450SixthAnalytic.W1.a0 <
      outerCoefficient C450SixthAnalytic.W0 ⟨-1,-31/32⟩+C450SixthAnalytic.W1.a0 := by
  norm_num [outerCoefficient,firstCoeff,secondCoeff,thirdCoeff,signedFactor,
    C450SixthAnalytic.W0,C450SixthAnalytic.W1,C450SixthAnalytic.sixth,
    c450Segs,TenSeg.W0,TenSeg.W1]
theorem negative_hub_domain_rejected :
    ¬(c450Cq (!₂[0,(7/10:ℝ)]:Point) (-1/10) ≤ outerV (!₂[0,(7/10:ℝ)]:Point)) := by
  have hd : (!₂[0,(7/10:ℝ)]:Point)-(!₂[-1/10,0]:Point) ≠ 0 := by
    intro hh
    have h0 := congrArg (fun x : Point => x 0) hh
    norm_num at h0
  have hp := norm_pos_iff.mpr hd
  have hv : outerV (!₂[0,(7/10:ℝ)]:Point) = 0 := by simp [outerV]
  have hq : 0 < c450Cq (!₂[0,(7/10:ℝ)]:Point) (-1/10) := by
    have hn : (!₂[0,(7/10:ℝ)]:Point) 0-(-1/10:ℝ) = 1/10 := by norm_num
    unfold c450Cq
    rw [hn]
    exact div_pos (by norm_num) hp
  rw [hv]
  exact not_le_of_gt hq
theorem zero_hub_direction (c : Point) : c450Cq c 0 = outerV c := by
  have hz : (!₂[0,0]:Point) = 0 := by
    ext i
    fin_cases i <;> simp
  simp [c450Cq,outerV,hz]
end N11Formalization.C450NonconstantOuterControls
#print axioms N11Formalization.C450NonconstantOuterControls.actual_sixth_not_zero
#print axioms N11Formalization.C450NonconstantOuterControls.wrong_sign_factor_rejected
#print axioms N11Formalization.C450NonconstantOuterControls.correct_sign_factor
#print axioms N11Formalization.C450NonconstantOuterControls.missing_cubic_domain_rejected
#print axioms N11Formalization.C450NonconstantOuterControls.inflated_capacity_rejected
#print axioms N11Formalization.C450NonconstantOuterControls.negative_hub_domain_rejected
#print axioms N11Formalization.C450NonconstantOuterControls.zero_hub_direction
