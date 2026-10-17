import N11Formalization.SourceTieForceTransport

/-! Actual signed45 graph centre-force functional vanishes, derived from the
real full23 stationary physical objective. No graph-force hypothesis is used.
Converting this functional to each actual SourceN2 centre coordinate row is a
separate finite incidence readout, not a new stationarity assumption. -/
set_option autoImplicit false
namespace N11Formalization.SourceTotalCentreForce
open N11Formalization CartesianReflectionSpace SourceCentreCovector
open SourceFaceForceTransport SourceTieForceTransport
noncomputable section

private theorem reflect_radius (v : Full) : reflect v 22=v 22 := rfl

theorem averagedInterior_force (v : Full) :
    FullCartesianDual.averagedDerivative v=
      v 22*(1-∑ j : Fin 5,PhysicalInteriorObjective.weight j)+
        totalFaceForce v/SourceExactRoot.sourceRoot 6 := by
  simp only [FullCartesianDual.averagedDerivative,smul_apply,add_apply,
    ContinuousLinearMap.comp_apply,reflectCLM_apply,
    ← PhysicalInteriorObjective.physicalDerivative_eq_length,smul_eq_mul]
  rw [physical_force_covector,physical_force_covector,totalFaceForce_average,reflect_radius]
  ring

private theorem tieTerm_formula (j : Fin 5) (v : Full) :
    BoundaryGapConversion.averagedTieDerivative (BoundaryGapConversion.representative j) v=
      (2 : ℝ)⁻¹*
        (tieForce (BoundaryGapConversion.representative j) v+
          tieForce (BoundaryGapConversion.representative j) (reflect v)) /
            SourceExactRoot.sourceRoot 6-v 22 := by
  simp only [BoundaryGapConversion.averagedTieDerivative,smul_apply,add_apply,
    ContinuousLinearMap.comp_apply,reflectCLM_apply,BoundaryGapConversion.rawDerivative,smul_eq_mul]
  rw [representative_tie_radius_force,representative_tie_radius_force,reflect_radius]
  ring

theorem averagedTie_force (v : Full) :
    (∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j*
      BoundaryGapConversion.averagedTieDerivative (BoundaryGapConversion.representative j) v)=
        totalTieForce v/SourceExactRoot.sourceRoot 6-
          v 22*(∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j) := by
  simp_rw [tieTerm_formula,mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [← mul_div_assoc]
  rw [← Finset.sum_div]
  have hc : (∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j*
      ((2 : ℝ)⁻¹*(tieForce (BoundaryGapConversion.representative j) v+
        tieForce (BoundaryGapConversion.representative j) (reflect v))))=totalTieForce v := by
    rw [totalTieForce_average]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp only [mul_left_comm (PhysicalBoundaryStationarity.tieWeight _) ((2 : ℝ)⁻¹),
      ← Finset.mul_sum]
  rw [hc,← Finset.sum_mul]
  ring

/-- All actual signed45 centre forces tested against every independent centre
velocity v vanish. This is derived from real fderiv=0 and signed mass1. -/
theorem totalCentreForce_zero (v : Full) : totalFaceForce v+totalTieForce v=0 := by
  have hs := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 5))) (fun j _ =>
    (BoundaryGapConversion.averagedTie_hasFDerivAt (BoundaryGapConversion.representative j)
      (BoundaryGapConversion.representative_active j)).const_smul (PhysicalBoundaryStationarity.tieWeight j))
  have h := PhysicalInteriorObjective.averagedPhysicalObjective_hasFDerivAt.add hs
  change HasFDerivAt PhysicalBoundaryStationarity.stationaryObjective
    (FullCartesianDual.averagedDerivative+
      ∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j •
        BoundaryGapConversion.averagedTieDerivative (BoundaryGapConversion.representative j))
    FullCartesianResidual.sourcePoint at h
  have hz := h.fderiv.symm.trans PhysicalBoundaryStationarity.stationary_source_fderiv
  have he := congrArg (fun d : Full →L[ℝ] ℝ => d v) hz
  simp only [add_apply,sum_apply,smul_apply,smul_eq_mul,zero_apply] at he
  rw [averagedInterior_force,averagedTie_force] at he
  have hm := PhysicalBoundaryStationarity.signed_mass_one
  have hmass : (1-∑ j : Fin 5,PhysicalInteriorObjective.weight j) =
      ∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j := by linarith
  rw [hmass] at he
  have hquot : (totalFaceForce v+totalTieForce v)/SourceExactRoot.sourceRoot 6=0 := by
    rw [add_div]
    linarith
  exact (div_eq_zero_iff).mp hquot |>.resolve_right (ne_of_gt SourceExactRoot.sourceRadius_pos)

end
end N11Formalization.SourceTotalCentreForce
#check @N11Formalization.SourceTotalCentreForce.totalCentreForce_zero
#print axioms N11Formalization.SourceTotalCentreForce.totalCentreForce_zero
