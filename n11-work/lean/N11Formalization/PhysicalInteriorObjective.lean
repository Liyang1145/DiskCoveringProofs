import N11Formalization.SourceCentralDerivative
import N11Formalization.FullCartesianDual
import N11Formalization.MuRootPositive

/-!
All FIVE actual interior LENGTH residuals are converted to their constructed
physical circumradius excess functions at the SAME source. The representative
physical weights are strictly positive from root multipliers and actual c>0.
The physical objective has the same source derivative as the real full
LENGTH objective; the boundary/tie conversion and B2 force chain remain open.
-/
set_option autoImplicit false
namespace N11Formalization.PhysicalInteriorObjective
open N11Formalization CartesianReflectionSpace
noncomputable section

def conversion (j : Fin 5) : ℝ :=
  ![SourceFanConversion.sourceConversion 1, SourceFanConversion.sourceConversion 2,
    SourceFanConversion.sourceConversion 3, SourceFanConversion.sourceConversion 8,
    SourceCentralGeometry.conversion] j

def radiusRow (j : Fin 5) : Full → ℝ :=
  ![SourceFanRadiusDerivative.radiusExcess 1, SourceFanRadiusDerivative.radiusExcess 2,
    SourceFanRadiusDerivative.radiusExcess 3, SourceFanRadiusDerivative.radiusExcess 8,
    SourceCentralDerivative.radiusExcess] j

def weight (j : Fin 5) : ℝ := -(last5 SourceExactRoot.sourceRoot j)*conversion j

theorem conversion_pos (j : Fin 5) : 0<conversion j := by
  fin_cases j
  · exact SourceFanConversion.sourceConversion_pos 1 (by simp)
  · exact SourceFanConversion.sourceConversion_pos 2 (by simp)
  · exact SourceFanConversion.sourceConversion_pos 3 (by simp)
  · exact SourceFanConversion.sourceConversion_pos 8 (by simp)
  · exact SourceCentralGeometry.conversion_pos

theorem weight_pos (j : Fin 5) : 0<weight j :=
  mul_pos (neg_pos.mpr (MuRootPositive.last5_lt_zero j)) (conversion_pos j)

theorem radiusRow_smooth (j : Fin 5) :
    ContDiffAt ℝ 1 (radiusRow j) FullCartesianResidual.sourcePoint := by
  have hr : ContDiffAt ℝ 1 (fun x : Full => x 22) FullCartesianResidual.sourcePoint := by
    fun_prop
  fin_cases j
  · exact (SourceFanCircumradius.fanRadius_source_smooth 1 (by simp)).sub hr
  · exact (SourceFanCircumradius.fanRadius_source_smooth 2 (by simp)).sub hr
  · exact (SourceFanCircumradius.fanRadius_source_smooth 3 (by simp)).sub hr
  · exact (SourceFanCircumradius.fanRadius_source_smooth 8 (by simp)).sub hr
  · exact SourceCentralGeometry.centralRadius_source_smooth.sub hr

theorem length_row_conversion (j : Fin 5) (v : Full) :
    fderiv ℝ (fun x : Full => FullCartesianResidual.residualFull x j)
      FullCartesianResidual.sourcePoint v =
      conversion j * fderiv ℝ (radiusRow j) FullCartesianResidual.sourcePoint v := by
  fin_cases j
  · exact SourceFanRadiusDerivative.length_to_circumradius 1 (by simp) v
  · exact SourceFanRadiusDerivative.length_to_circumradius 2 (by simp) v
  · exact SourceFanRadiusDerivative.length_to_circumradius 3 (by simp) v
  · exact SourceFanRadiusDerivative.length_to_circumradius 8 (by simp) v
  · exact SourceCentralDerivative.length_to_circumradius v

def physicalObjective (x : Full) : ℝ := x 22+∑ j : Fin 5, weight j*radiusRow j x

def physicalDerivative : Full →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ)+
    ∑ j : Fin 5, weight j • fderiv ℝ (radiusRow j) FullCartesianResidual.sourcePoint

theorem physicalObjective_hasFDerivAt :
    HasFDerivAt physicalObjective physicalDerivative FullCartesianResidual.sourcePoint := by
  have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 5))) (fun j _ =>
    ((radiusRow_smooth j).differentiableAt (by norm_num)).hasFDerivAt.const_smul (weight j))
  exact (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt.add hs

private theorem objectiveLength_hasFDerivAt :
    HasFDerivAt FullCartesianResidual.objectiveFull
      ((ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ)-
        ∑ j : Fin 5, last5 SourceExactRoot.sourceRoot j •
          fderiv ℝ (fun x : Full => FullCartesianResidual.residualFull x j)
            FullCartesianResidual.sourcePoint)
      FullCartesianResidual.sourcePoint := by
  have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 5))) (fun j _ =>
    (((contDiffAt_pi.mp FullCartesianResidual.residualFull_source_smooth) j).differentiableAt
      (by norm_num)).hasFDerivAt.const_smul (last5 SourceExactRoot.sourceRoot j))
  exact (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt.sub hs

/-- Actual five-row physical objective derivative, not a conditional wrapper.
Every radius/length gradient conversion, including central, is paid above. -/
theorem physicalDerivative_eq_length :
    physicalDerivative=FullCartesianDual.fullDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  rw [show FullCartesianDual.fullDerivative =
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ)-
        ∑ j : Fin 5, last5 SourceExactRoot.sourceRoot j •
          fderiv ℝ (fun x : Full => FullCartesianResidual.residualFull x j)
            FullCartesianResidual.sourcePoint from objectiveLength_hasFDerivAt.fderiv]
  simp only [physicalDerivative, add_apply, sub_apply, sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
    congrArg (fun r : ℝ => last5 SourceExactRoot.sourceRoot j*r) (length_row_conversion j v))]
  simp only [weight, neg_mul, mul_assoc, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Independent-R calibration: the constructed circumradii depend on centres
only, so each radius-excess derivative is exactly -1 in coordinate22. -/
theorem radiusRow_radius_direction (j : Fin 5) :
    fderiv ℝ (radiusRow j) FullCartesianResidual.sourcePoint
      (Pi.single 22 1 : Full) = -1 := by
  have hring (k : Fin 9) : FullCartesianResidual.ring (Pi.single 22 1 : Full) k=0 := by
    have hi0 : (⟨2*k.val,by omega⟩ : Fin 23)≠22 := by
      intro h
      have hv := congrArg Fin.val h
      change 2*k.val=22 at hv
      omega
    have hi1 : (⟨2*k.val+1,by omega⟩ : Fin 23)≠22 := by
      intro h
      have hv := congrArg Fin.val h
      change 2*k.val+1=22 at hv
      omega
    ext i
    fin_cases i
    · change (Pi.single 22 (1 : ℝ) : Full) ⟨2*k.val,by omega⟩=0
      simp [Pi.single_apply,hi0,Ne.symm hi0]
    · change (Pi.single 22 (1 : ℝ) : Full) ⟨2*k.val+1,by omega⟩=0
      simp [Pi.single_apply,hi1,Ne.symm hi1]
  have hA : FullCartesianResidual.hubA (Pi.single 22 1 : Full)=0 := by
    ext i
    fin_cases i <;> norm_num [FullCartesianResidual.hubA,Pi.single_apply,Fin.ext_iff]
  have hB : FullCartesianResidual.hubB (Pi.single 22 1 : Full)=0 := by
    ext i
    fin_cases i <;> norm_num [FullCartesianResidual.hubB,Pi.single_apply,Fin.ext_iff]
  have hfan (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
      fderiv ℝ (SourceFanRadiusDerivative.radiusExcess k) FullCartesianResidual.sourcePoint
        (Pi.single 22 1 : Full) = -1 := by
    rw [SourceFanRadiusDerivative.radiusExcess_source_fderiv k hk,
      SourceFanRadiusDerivative.fanRadius_source_fderiv k hk]
    have hhub : SourceFanLengthCovector.fullHub k (Pi.single 22 1 : Full)=0 := by
      unfold SourceFanLengthCovector.fullHub
      split_ifs <;> assumption
    simp only [SourceFanRadiusDerivative.left_ringData,SourceFanRadiusDerivative.right_ringData,
      hring,hhub,inner_zero_right,mul_zero,add_zero,neg_zero,zero_div,Pi.single_eq_same,zero_sub]
  fin_cases j
  · exact hfan 1 (by simp)
  · exact hfan 2 (by simp)
  · exact hfan 3 (by simp)
  · exact hfan 8 (by simp)
  · have hR : HasFDerivAt SourceCentralDerivative.radiusExcess
        (fderiv ℝ SourceCentralGeometry.centralRadius FullCartesianResidual.sourcePoint-
          (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ))
        FullCartesianResidual.sourcePoint :=
      (SourceCentralGeometry.centralRadius_source_smooth.differentiableAt
        (by norm_num)).hasFDerivAt.sub
        (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt
    change fderiv ℝ SourceCentralDerivative.radiusExcess FullCartesianResidual.sourcePoint
      (Pi.single 22 1 : Full) = -1
    rw [hR.fderiv]
    simp only [sub_apply,ContinuousLinearMap.proj_apply,Pi.single_eq_same]
    rw [SourceCentralDerivative.centralRadius_fderiv]
    simp only [hA,hB,hring,inner_zero_right,mul_zero,add_zero,neg_zero,zero_div,zero_sub]

theorem physical_radius_mass :
    physicalDerivative (Pi.single 22 1 : Full)=1-∑ j : Fin 5,weight j := by
  simp only [physicalDerivative,add_apply,sum_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.proj_apply,Pi.single_eq_same,radiusRow_radius_direction]
  simp [sub_eq_add_neg,mul_neg,Finset.sum_neg_distrib]

def averagedPhysicalObjective (x : Full) : ℝ :=
  (physicalObjective x+physicalObjective (reflect x))/2

theorem averagedPhysicalObjective_hasFDerivAt :
    HasFDerivAt averagedPhysicalObjective FullCartesianDual.averagedDerivative
      FullCartesianResidual.sourcePoint := by
  have hf := physicalObjective_hasFDerivAt
  have hf' : HasFDerivAt physicalObjective physicalDerivative
      (reflect FullCartesianResidual.sourcePoint) := by
    rw [show reflect FullCartesianResidual.sourcePoint=FullCartesianResidual.sourcePoint from source_fixed]
    exact hf
  have hs := (hf.add (hf'.comp FullCartesianResidual.sourcePoint reflectCLM.hasFDerivAt)).const_smul
    ((2 : ℝ)⁻¹)
  have he : averagedPhysicalObjective=(fun x : Full => (2 : ℝ)⁻¹ *
      (physicalObjective x+physicalObjective (reflect x))) := by
    funext x
    simp only [averagedPhysicalObjective,div_eq_mul_inv]
    ring
  rw [physicalDerivative_eq_length] at hs
  change HasFDerivAt (fun x : Full => (2 : ℝ)⁻¹ *
      (physicalObjective x+physicalObjective (reflect x)))
      FullCartesianDual.averagedDerivative FullCartesianResidual.sourcePoint at hs
  rwa [← he] at hs

theorem actual_physical_interior_dual (v : Full) :
    fderiv ℝ averagedPhysicalObjective FullCartesianResidual.sourcePoint v =
      ∑ j : Fin 5, BoundaryChartDual.multiplier
        (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
          CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
        FullCartesianDual.invariantBoundary v j := by
  rw [averagedPhysicalObjective_hasFDerivAt.fderiv]
  have h := FullCartesianDual.actual_full_cartesian_dual v
  rw [FullCartesianDual.averagedDerivative_hasFDerivAt.fderiv] at h
  exact h

end
end N11Formalization.PhysicalInteriorObjective
#check @N11Formalization.PhysicalInteriorObjective.weight_pos
#check @N11Formalization.PhysicalInteriorObjective.actual_physical_interior_dual
#print axioms N11Formalization.PhysicalInteriorObjective.actual_physical_interior_dual
