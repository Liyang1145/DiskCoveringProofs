import N11Formalization.SourceAllFaceBalance

/-! Exact self-reflected source fan8 geometry and beta symmetry. This source
identity is essential when replacing an averaged derivative by one actual
face block of orbit-size1; it is not inferred from dimension counting. -/
set_option autoImplicit false
namespace N11Formalization.SourceSelfFaceSymmetry
open N11Formalization SourceFaceReflection PinTangentGeometry
noncomputable section

theorem inner_flip (p q : Point) : inner ℝ (flip p) (flip q)=inner ℝ p q := by
  rw [inner_coords,inner_coords]
  simp [SourceFaceReflection.flip]

theorem inner_flip_left (p q : Point) : inner ℝ (flip p) q=inner ℝ p (flip q) := by
  have h := inner_flip p (flip q)
  rw [SourceFaceReflection.flip_flip] at h
  exact h

theorem det_flip (p q : Point) : det (flip p) (flip q)=-det p q := by
  unfold det
  simp only [SourceFaceReflection.flip,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring
theorem det_swap (p q : Point) : det q p=-det p q := by unfold det; ring

theorem ring8_reflection : flip (ringCenter SourceExactRoot.sourceRoot 8)=ringCenter SourceExactRoot.sourceRoot 0 := by
  have h := actual_site_reflection 8
  simpa [siteMirror,centersOfRoot] using h.symm
theorem ring0_reflection : flip (ringCenter SourceExactRoot.sourceRoot 0)=ringCenter SourceExactRoot.sourceRoot 8 := by
  rw [← ring8_reflection,SourceFaceReflection.flip_flip]
theorem hub1_reflection : flip (hub1 SourceExactRoot.sourceRoot)=hub1 SourceExactRoot.sourceRoot := by
  ext i
  fin_cases i <;> simp [SourceFaceReflection.flip,hub1]

theorem endpoint8_reflection : flip (arcEnd SourceExactRoot.sourceRoot 8)=arcEnd SourceExactRoot.sourceRoot 8 := by
  rw [arcEnd_eq_circleMap,show thetaOf (angleVec SourceExactRoot.sourceRoot) 8+
    angleVec SourceExactRoot.sourceRoot 8=Real.pi from arcHiG_eight _]
  ext i
  fin_cases i <;> simp [SourceFaceReflection.flip,circleMap]

theorem center8_reflection : flip (Uvec SourceExactRoot.sourceRoot 8)=Uvec SourceExactRoot.sourceRoot 8 := by
  have he : Uvec SourceExactRoot.sourceRoot 8 =
      ringCenter SourceExactRoot.sourceRoot 8+ringCenter SourceExactRoot.sourceRoot 0-
      arcEnd SourceExactRoot.sourceRoot 8 := by rw [Uvec,nd_fin_succ_8]
  rw [he]
  change flipLinear (ringCenter SourceExactRoot.sourceRoot 8+ringCenter SourceExactRoot.sourceRoot 0-
      arcEnd SourceExactRoot.sourceRoot 8)=_
  rw [map_sub,map_add]
  simp only [flipLinear_apply,ring8_reflection,ring0_reflection,endpoint8_reflection]
  abel

theorem normal8_P_reflection : flip (SourceFanLengthCovector.normalP 8)=SourceFanLengthCovector.normalQ 8 := by
  simp only [SourceFanLengthCovector.normalP,SourceFanLengthCovector.normalQ,flip_sub,
    center8_reflection,ring8_reflection,nd_fin_succ_8]
theorem normal8_Q_reflection : flip (SourceFanLengthCovector.normalQ 8)=SourceFanLengthCovector.normalP 8 := by
  rw [← normal8_P_reflection,SourceFaceReflection.flip_flip]
theorem normal8_H_reflection : flip (SourceFanLengthCovector.normalH 8)=SourceFanLengthCovector.normalH 8 := by
  have hhub : SourceFanLengthCovector.sourceHub 8=hub1 SourceExactRoot.sourceRoot := by
    simp [SourceFanLengthCovector.sourceHub]
  simp only [SourceFanLengthCovector.normalH,hhub,flip_sub,center8_reflection,hub1_reflection]

theorem sourceA8_eq_sourceB8 : SourceFanLengthCovector.sourceA 8=SourceFanLengthCovector.sourceB 8 := by
  have hN := det_flip (SourceFanLengthCovector.normalH 8) (SourceFanLengthCovector.normalQ 8)
  rw [normal8_H_reflection,normal8_Q_reflection,det_swap (SourceFanLengthCovector.normalP 8)
    (SourceFanLengthCovector.normalH 8)] at hN
  have hn : det (SourceFanLengthCovector.normalH 8) (SourceFanLengthCovector.normalQ 8)=
      det (SourceFanLengthCovector.normalP 8) (SourceFanLengthCovector.normalH 8) := by linarith
  unfold SourceFanLengthCovector.sourceA SourceFanLengthCovector.sourceB
    SourceFanLengthCovector.coefficientA SourceFanLengthCovector.coefficientB
  rw [hn]

theorem beta8_symmetry : SourceFanConversion.betaP 8=SourceFanConversion.betaQ 8 := by
  unfold SourceFanConversion.betaP SourceFanConversion.betaQ
  rw [sourceA8_eq_sourceB8]

end
end N11Formalization.SourceSelfFaceSymmetry
#check @N11Formalization.SourceSelfFaceSymmetry.beta8_symmetry
#print axioms N11Formalization.SourceSelfFaceSymmetry.beta8_symmetry
