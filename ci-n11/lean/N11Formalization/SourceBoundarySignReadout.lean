import N11Formalization.SourceCentreB2Readout

/-! Actual boundary-multiplier sign readout at the source. The orbit3
multiplier is isolated by the independent central-ring WIDTH direction; its
positivity proof uses actual source beta signs and coordinate interval margin.
This does NOT yet pay the other four physical tie weights. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundarySignReadout
open N11Formalization CartesianReflectionSpace SourceFrameVelocity SourceFaceReflection
noncomputable section

def widthFour : SourceFrameVelocity.Frame := Pi.single 4 1
def xUnit : Point := !₂[1,0]

theorem widthFour_velocities (k : Fin 9) :
    SourceFrameVelocity.velocity k widthFour=
      if k=4 then SourceFrameVelocity.slopeA 4 • xUnit else 0 := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [SourceFrameVelocity.velocity,SourceFrameVelocity.radialVelocity,widthFour,xUnit,
      PhysicalResidualFrame.widths,PhysicalResidualFrame.directions,thetaOf_four,
      Pi.single_apply,Fin.ext_iff]

theorem widthFour_sites (i : Fin 11) :
    siteFull (frameJac widthFour) i=
      if i=4 then SourceFrameVelocity.slopeA 4 • xUnit else 0 := by
  have hr (k : Fin 9) :
      FullCartesianResidual.ring (frameJac widthFour) k=
        if k=4 then SourceFrameVelocity.slopeA 4 • xUnit else 0 := by
    rw [ring_frameJac,widthFour_velocities]
  have hA : FullCartesianResidual.hubA (frameJac widthFour)=0 := by
    change (!₂[0,0] : Point)=0
    ext q
    fin_cases q <;> rfl
  have hB : FullCartesianResidual.hubB (frameJac widthFour)=0 := by
    change (!₂[0,0] : Point)=0
    ext q
    fin_cases q <;> rfl
  fin_cases i <;> simp [siteFull,hr,hA,hB,Fin.ext_iff]

theorem source_ring4_margin :
    (3 : ℝ)/10≤(ringCenter SourceExactRoot.sourceRoot 4) 0-(Uvec SourceExactRoot.sourceRoot 3) 0 := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hlo := (ndRingBox_mem hb 4 0).1
  have hhi := (ndUvecBox_mem hb 3 0).2
  have hread : (3/10 : ℚ)≤(ndRingBox ndBox 4 0).lo-(ndUvecBox ndBox 3 0).hi := by nd_eval
  have hcast : (3 : ℝ)/10≤
      ((ndRingBox ndBox 4 0).lo : ℝ)-((ndUvecBox ndBox 3 0).hi : ℝ) := by
    have h : (((3/10 : ℚ) : ℝ))≤
        (((ndRingBox ndBox 4 0).lo-(ndUvecBox ndBox 3 0).hi : ℚ) : ℝ) :=
      (Rat.cast_le).mpr hread
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using h
  linarith

def positiveTerm : ℝ :=
  PhysicalInteriorObjective.weight 2*SourceFanConversion.betaQ 3*
    ((ringCenter SourceExactRoot.sourceRoot 4) 0-(Uvec SourceExactRoot.sourceRoot 3) 0)*
      SourceFrameVelocity.slopeA 4

theorem positiveTerm_pos : 0<positiveTerm := by
  have hb := (SourceFanBarycentricSigns.source_betas_pos 3 (by simp)).2.1
  have hc : 0<(ringCenter SourceExactRoot.sourceRoot 4) 0-(Uvec SourceExactRoot.sourceRoot 3) 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ)<3/10) source_ring4_margin
  have hA : 0<SourceFrameVelocity.slopeA 4 :=
    SourceWidthNondegenerate.source_widthSlope_pos 4
  exact mul_pos (mul_pos (mul_pos (PhysicalInteriorObjective.weight_pos 2) hb) hc) hA

theorem widthFour_face_force :
    (∑ j : Fin 5,PhysicalInteriorObjective.weight j*
      SourceCentreCovector.representativeForce j (frameJac widthFour))=positiveTerm := by
  have he (j : Fin 5) :
      SourceCentreCovector.representativeForce j (frameJac widthFour)=
        if j=2 then SourceFanConversion.betaQ 3*
          ((ringCenter SourceExactRoot.sourceRoot 4) 0-(Uvec SourceExactRoot.sourceRoot 3) 0)*
          SourceFrameVelocity.slopeA 4 else 0 := by
    unfold SourceCentreCovector.representativeForce
    simp_rw [widthFour_sites]
    fin_cases j <;> simp [SourceRepresentativeFaceBalance.beta,SourceRepresentativeFaceBalance.vertices,
      SourceRepresentativeFaceBalance.center,SourceRepresentativeFaceBalance.faceIndex,
      ResumeLocalIncidence.sourceFaces,Fin.sum_univ_succ,Fin.ext_iff,
      PinTangentGeometry.inner_coords,xUnit,smul_eq_mul] <;> ring
  simp_rw [he]
  rw [Finset.sum_eq_single (2 : Fin 5)]
  · simp only [ite_true]
    unfold positiveTerm
    ring
  · intro b _ hb
    rw [if_neg hb,mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

theorem widthFour_objective_derivative :
    fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint widthFour=
      positiveTerm/SourceExactRoot.sourceRoot 6 := by
  have hf := SourceCentreCovector.physical_force_covector (frameJac widthFour)
  have hF : FullCartesianDual.fullDerivative (frameJac widthFour)=
      fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint widthFour :=
    FullCartesianDual.fullDerivative_frame widthFour
  rw [PhysicalInteriorObjective.physicalDerivative_eq_length,hF] at hf
  rw [widthFour_face_force,frameJac_radius] at hf
  have hR : widthFour 11=0 := by simp [widthFour,Pi.single_apply,Fin.ext_iff]
  simpa only [hR,zero_mul,zero_add] using hf

/-- One actual source sign paid analytically and by a strict root-box margin.
No numerical derivative, stationarity or coefficient sign premise remains. -/
theorem boundaryMultiplier_three_neg : PhysicalBoundaryStationarity.boundaryMultiplier 3<0 := by
  have hdual := TrueResidualFrame.objectiveTrue_boundary_dual widthFour
  have heval : fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint widthFour=
      -PhysicalBoundaryStationarity.boundaryMultiplier 3 := by
    change fderiv ℝ TrueResidualFrame.objectiveTrue TruePinFrameDifferential.sourcePoint widthFour=
      -PhysicalBoundaryStationarity.boundaryMultiplier 3
    rw [hdual]
    simp [PhysicalBoundaryStationarity.boundaryMultiplier,BoundaryChartLinear.boundary,widthFour,
      Fin.sum_univ_succ,Pi.single_apply,Fin.ext_iff,CoupledRadialFrame.sourcePoint,
      TruePinFrameDifferential.sourcePoint]
  have hp : 0<fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint widthFour := by
    rw [widthFour_objective_derivative]
    exact div_pos positiveTerm_pos SourceExactRoot.sourceRadius_pos
  rw [heval] at hp
  linarith

theorem tieWeight_three_pos : 0<PhysicalBoundaryStationarity.tieWeight 3 :=
  mul_pos (neg_pos.mpr boundaryMultiplier_three_neg) (SourceBoundaryWeights.radiusScale_pos 3)

/-- Four actual source spokes now positive unconditionally; the two mirrored
tie indices3/4 share the source representative weight whose sign was paid. -/
theorem spokes_three_four_pos (k : Fin 9) (hk : k=3 ∨ k=4) (s : Fin 2) :
    0<SourceSignedStressAssembly.stress (.inl (k,s)) := by
  apply (SourceSignedStressAssembly.spoke_positive_iff k s).mpr
  rcases hk with rfl | rfl <;> exact tieWeight_three_pos

/-- The actual remaining positivity obligation is precisely four source
boundary signs, rather than all five. This equivalence does NOT pay those4. -/
theorem remaining_stress_signs_iff :
    (∀ e : ResumeLocalIncidence.SourceEdge,0<SourceSignedStressAssembly.stress e) ↔
      (∀ j : Fin 5,j≠3 → 0<PhysicalBoundaryStationarity.tieWeight j) := by
  rw [SourceSignedStressAssembly.stress_positive_iff]
  constructor
  · intro h j _
    exact h j
  · intro h j
    by_cases hj : j=3
    · rw [hj]
      exact tieWeight_three_pos
    · exact h j hj

end
end N11Formalization.SourceBoundarySignReadout
#check @N11Formalization.SourceBoundarySignReadout.boundaryMultiplier_three_neg
#check @N11Formalization.SourceBoundarySignReadout.tieWeight_three_pos
#check @N11Formalization.SourceBoundarySignReadout.spokes_three_four_pos
#check @N11Formalization.SourceBoundarySignReadout.remaining_stress_signs_iff
#print axioms N11Formalization.SourceBoundarySignReadout.tieWeight_three_pos
