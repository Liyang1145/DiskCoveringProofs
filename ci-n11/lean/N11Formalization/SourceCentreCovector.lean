import N11Formalization.SourceSignedStressAssembly

/-! Binding the actual representative circumradius differential to the actual
source-face centre forces, in centre-minus-circumcentre conventions. These
functions are consumers of real fderiv results, not new stationarity premises.
Full reflected centre-force assembly remains a downstream obligation. -/
set_option autoImplicit false
namespace N11Formalization.SourceCentreCovector
open N11Formalization CartesianReflectionSpace SourceFaceReflection
open ResumeLocalIncidence
noncomputable section

def representativeForce (j : Fin 5) (v : Full) : ℝ :=
  ∑ t : Fin 3, SourceRepresentativeFaceBalance.beta j t *
    inner ℝ
      (SourceRepresentativeFaceBalance.vertices j t-SourceRepresentativeFaceBalance.center j)
      (siteFull v (sourceFaces (SourceRepresentativeFaceBalance.faceIndex j) t))

theorem source_site_velocity_ring (k : Fin 9) (v : Full) :
    siteFull v ⟨k.val,by omega⟩=FullCartesianResidual.ring v k := by
  fin_cases k <;> rfl

private theorem fan_row (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) (v : Full) :
    fderiv ℝ (SourceFanRadiusDerivative.radiusExcess k) FullCartesianResidual.sourcePoint v =
      -(SourceFanConversion.betaP k * inner ℝ (SourceFanLengthCovector.normalP k)
          (FullCartesianResidual.ring v k)+
        SourceFanConversion.betaQ k * inner ℝ (SourceFanLengthCovector.normalQ k)
          (FullCartesianResidual.ring v (k+1))+
        SourceFanConversion.betaH k * inner ℝ (SourceFanLengthCovector.normalH k)
          (SourceFanLengthCovector.fullHub k v)) / SourceExactRoot.sourceRoot 6-v 22 := by
  rw [SourceFanRadiusDerivative.radiusExcess_source_fderiv k hk,
    SourceFanRadiusDerivative.fanRadius_source_fderiv k hk]
  simp only [SourceFanRadiusDerivative.left_ringData,SourceFanRadiusDerivative.right_ringData]

private theorem central_excess_row (v : Full) :
    fderiv ℝ SourceCentralDerivative.radiusExcess FullCartesianResidual.sourcePoint v =
      -(SourceCentralGeometry.betaP*inner ℝ SourceCentralGeometry.nP (FullCartesianResidual.hubA v)+
        SourceCentralGeometry.betaQ*inner ℝ SourceCentralGeometry.nQ (FullCartesianResidual.hubB v)+
        SourceCentralGeometry.betaH*inner ℝ SourceCentralGeometry.nH (FullCartesianResidual.ring v 6)) /
        SourceExactRoot.sourceRoot 6-v 22 := by
  have h := (SourceCentralGeometry.centralRadius_source_smooth.differentiableAt
    (by norm_num)).hasFDerivAt.sub
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt SourceCentralDerivative.radiusExcess
    (fderiv ℝ SourceCentralGeometry.centralRadius FullCartesianResidual.sourcePoint-
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ))
    FullCartesianResidual.sourcePoint at h
  rw [h.fderiv]
  simp only [sub_apply,ContinuousLinearMap.proj_apply]
  rw [SourceCentralDerivative.centralRadius_fderiv]
  rfl

/-- Actual representative physical radius derivative = actual source force
covector/R-dR. No derivative, beta, source-circle or source-index hypotheses. -/
theorem representative_radius_force (j : Fin 5) (v : Full) :
    fderiv ℝ (PhysicalInteriorObjective.radiusRow j) FullCartesianResidual.sourcePoint v =
      representativeForce j v/SourceExactRoot.sourceRoot 6-v 22 := by
  have hf1 := fan_row 1 (by simp) v
  have hf2 := fan_row 2 (by simp) v
  have hf3 := fan_row 3 (by simp) v
  have hf8 := fan_row 8 (by simp) v
  have hc := central_excess_row v
  fin_cases j
  all_goals
    simp only [PhysicalInteriorObjective.radiusRow,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk]
  · rw [hf1]
    unfold representativeForce
    simp [SourceRepresentativeFaceBalance.beta,SourceRepresentativeFaceBalance.vertices,
      SourceRepresentativeFaceBalance.center,SourceRepresentativeFaceBalance.faceIndex,sourceFaces,
      siteFull,Fin.sum_univ_succ,SourceFanLengthCovector.normalP,SourceFanLengthCovector.normalQ,
      SourceFanLengthCovector.normalH,SourceFanLengthCovector.sourceHub,SourceFanLengthCovector.fullHub,
      nd_fin_succ_1,inner_sub_left,Fin.ext_iff]
    ring
  · rw [hf2]
    unfold representativeForce
    simp [SourceRepresentativeFaceBalance.beta,SourceRepresentativeFaceBalance.vertices,
      SourceRepresentativeFaceBalance.center,SourceRepresentativeFaceBalance.faceIndex,sourceFaces,
      siteFull,Fin.sum_univ_succ,SourceFanLengthCovector.normalP,SourceFanLengthCovector.normalQ,
      SourceFanLengthCovector.normalH,SourceFanLengthCovector.sourceHub,SourceFanLengthCovector.fullHub,
      nd_fin_succ_2,inner_sub_left,Fin.ext_iff]
    ring
  · rw [hf3]
    unfold representativeForce
    simp [SourceRepresentativeFaceBalance.beta,SourceRepresentativeFaceBalance.vertices,
      SourceRepresentativeFaceBalance.center,SourceRepresentativeFaceBalance.faceIndex,sourceFaces,
      siteFull,Fin.sum_univ_succ,SourceFanLengthCovector.normalP,SourceFanLengthCovector.normalQ,
      SourceFanLengthCovector.normalH,SourceFanLengthCovector.sourceHub,SourceFanLengthCovector.fullHub,
      nd_fin_succ_3,inner_sub_left,Fin.ext_iff]
    ring
  · rw [hf8]
    unfold representativeForce
    simp [SourceRepresentativeFaceBalance.beta,SourceRepresentativeFaceBalance.vertices,
      SourceRepresentativeFaceBalance.center,SourceRepresentativeFaceBalance.faceIndex,sourceFaces,
      siteFull,Fin.sum_univ_succ,SourceFanLengthCovector.normalP,SourceFanLengthCovector.normalQ,
      SourceFanLengthCovector.normalH,SourceFanLengthCovector.sourceHub,SourceFanLengthCovector.fullHub,
      nd_fin_succ_8,inner_sub_left,Fin.ext_iff]
    ring
  · rw [hc]
    unfold representativeForce
    simp [SourceRepresentativeFaceBalance.beta,SourceRepresentativeFaceBalance.vertices,
      SourceRepresentativeFaceBalance.center,SourceRepresentativeFaceBalance.faceIndex,sourceFaces,
      siteFull,Fin.sum_univ_succ,SourceCentralGeometry.nP,SourceCentralGeometry.nQ,
      SourceCentralGeometry.nH,inner_sub_left]
    ring

theorem physical_force_covector (v : Full) :
    PhysicalInteriorObjective.physicalDerivative v =
      v 22 * (1-∑ j : Fin 5,PhysicalInteriorObjective.weight j)+
        (∑ j : Fin 5,PhysicalInteriorObjective.weight j*representativeForce j v)/
          SourceExactRoot.sourceRoot 6 := by
  change v 22+(∑ j : Fin 5,PhysicalInteriorObjective.weight j*
    fderiv ℝ (PhysicalInteriorObjective.radiusRow j) FullCartesianResidual.sourcePoint v)=_
  simp_rw [representative_radius_force,mul_sub]
  simp only [← mul_div_assoc]
  rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_mul]
  ring

end
end N11Formalization.SourceCentreCovector
#check @N11Formalization.SourceCentreCovector.representative_radius_force
#check @N11Formalization.SourceCentreCovector.physical_force_covector
#print axioms N11Formalization.SourceCentreCovector.physical_force_covector
