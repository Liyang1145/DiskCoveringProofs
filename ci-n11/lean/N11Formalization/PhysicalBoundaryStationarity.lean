import N11Formalization.BoundaryGapConversion
import N11Formalization.PhysicalInteriorObjective

/-! Actual independently moving interior circumradius and unit-circle tie
radius branches now give a source stationary FULL Cartesian23 Lagrangian.
Interior representative weights are positive; boundary weights are exact
signed values, with their signs NOT yet asserted. This is not yet a positive
normalized SourceN2 stress or the unrestricted optimality theorem. -/
set_option autoImplicit false
namespace N11Formalization.PhysicalBoundaryStationarity
open N11Formalization CartesianReflectionSpace BoundaryGapConversion
noncomputable section

def boundaryMultiplier (j : Fin 5) : ℝ :=
  BoundaryChartDual.multiplier
    (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
      CoupledRadialFrame.sourcePoint (Pi.single i 1)) j

/-- Sign convention is explicit: the earlier dual is dObjective=Σm*dGap,
so the Lagrangian tie weight is -m*b, NOT m*b. Positivity is still unpaid. -/
def tieWeight (j : Fin 5) : ℝ :=
  -boundaryMultiplier j * SourceBoundaryWeights.radiusScale (representative j)

def stationaryObjective (x : Full) : ℝ :=
  PhysicalInteriorObjective.averagedPhysicalObjective x+
    ∑ j : Fin 5, tieWeight j*averagedTieExcess (representative j) x

theorem physical_covector_formula (v : Full) :
    FullCartesianDual.averagedDerivative v =
      ∑ j : Fin 5, boundaryMultiplier j *
        SourceBoundaryWeights.radiusScale (representative j) *
        averagedTieDerivative (representative j) v := by
  have hp := PhysicalInteriorObjective.actual_physical_interior_dual v
  rw [PhysicalInteriorObjective.averagedPhysicalObjective_hasFDerivAt.fderiv] at hp
  have hg (j : Fin 5) : FullCartesianDual.invariantBoundary v j =
      SourceBoundaryWeights.radiusScale (representative j) *
        averagedTieDerivative (representative j) v := by
    have h := full_gap_to_tie j v
    rw [(averagedTie_hasFDerivAt (representative j) (representative_active j)).fderiv] at h
    exact h
  rw [hp]
  apply Finset.sum_congr rfl
  intro j _
  rw [hg j]
  unfold boundaryMultiplier
  ring

theorem stationary_source_fderiv : fderiv ℝ stationaryObjective FullCartesianResidual.sourcePoint=0 := by
  have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 5))) (fun j _ =>
    (averagedTie_hasFDerivAt (representative j) (representative_active j)).const_smul (tieWeight j))
  have h := PhysicalInteriorObjective.averagedPhysicalObjective_hasFDerivAt.add hs
  change HasFDerivAt stationaryObjective
    (FullCartesianDual.averagedDerivative+
      ∑ j : Fin 5, tieWeight j • averagedTieDerivative (representative j))
    FullCartesianResidual.sourcePoint at h
  rw [h.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply,sum_apply,smul_apply,smul_eq_mul]
  rw [physical_covector_formula]
  simp only [tieWeight,neg_mul,mul_assoc,Finset.sum_neg_distrib]
  exact add_neg_cancel _

private theorem ring_radius_direction (k : Fin 9) :
    FullCartesianResidual.ring (Pi.single 22 1 : Full) k=0 := by
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
    simp [hi0]
  · change (Pi.single 22 (1 : ℝ) : Full) ⟨2*k.val+1,by omega⟩=0
    simp [hi1]

theorem reflect_radius_direction :
    reflect (Pi.single 22 1 : Full)=(Pi.single 22 1 : Full) := by
  funext i
  fin_cases i <;> norm_num [reflect,Pi.single_apply,Fin.ext_iff]

theorem tie_radius_direction (j : Fin 5) :
    averagedTieDerivative (representative j) (Pi.single 22 1 : Full)=-1 := by
  have hraw : rawDerivative (representative j) (Pi.single 22 1 : Full)=-1 := by
    rw [rawDerivative,excess_source_fderiv _ (representative_active j),
      SourceBoundaryTieDerivative.radiusFull_source_fderiv _ (representative_active j)]
    simp only [ring_radius_direction,inner_zero_right,mul_zero,add_zero,
      neg_zero,zero_div,Pi.single_eq_same,zero_sub]
  simp only [averagedTieDerivative,smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    reflectCLM_apply,reflect_radius_direction,hraw,smul_eq_mul]
  norm_num

/-- Exact signed mass normalization from the actual independent R column.
This does NOT imply boundary/tie weights are nonnegative. -/
theorem signed_mass_one :
    (∑ j : Fin 5, PhysicalInteriorObjective.weight j)+(∑ j : Fin 5, tieWeight j)=1 := by
  have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 5))) (fun j _ =>
    (averagedTie_hasFDerivAt (representative j) (representative_active j)).const_smul (tieWeight j))
  have h := PhysicalInteriorObjective.averagedPhysicalObjective_hasFDerivAt.add hs
  change HasFDerivAt stationaryObjective
    (FullCartesianDual.averagedDerivative+
      ∑ j : Fin 5, tieWeight j • averagedTieDerivative (representative j))
    FullCartesianResidual.sourcePoint at h
  have hz := h.fderiv.symm.trans stationary_source_fderiv
  have he := congrArg (fun d : Full →L[ℝ] ℝ => d (Pi.single 22 1 : Full)) hz
  have hrad : FullCartesianDual.averagedDerivative (Pi.single 22 1 : Full) =
      PhysicalInteriorObjective.physicalDerivative (Pi.single 22 1 : Full) := by
    simp only [FullCartesianDual.averagedDerivative,smul_apply,add_apply,
      ContinuousLinearMap.comp_apply,reflectCLM_apply,reflect_radius_direction,
      ← PhysicalInteriorObjective.physicalDerivative_eq_length,smul_eq_mul]
    ring
  simp only [add_apply,sum_apply,smul_apply,smul_eq_mul,zero_apply,
    hrad,PhysicalInteriorObjective.physical_radius_mass,tie_radius_direction,mul_neg_one,
    Finset.sum_neg_distrib] at he
  linarith

end
end N11Formalization.PhysicalBoundaryStationarity
#check @N11Formalization.PhysicalBoundaryStationarity.physical_covector_formula
#check @N11Formalization.PhysicalBoundaryStationarity.stationary_source_fderiv
#check @N11Formalization.PhysicalBoundaryStationarity.signed_mass_one
#print axioms N11Formalization.PhysicalBoundaryStationarity.stationary_source_fderiv
#print axioms N11Formalization.PhysicalBoundaryStationarity.signed_mass_one
