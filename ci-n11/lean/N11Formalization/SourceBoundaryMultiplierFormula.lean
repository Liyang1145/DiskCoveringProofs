import N11Formalization.SourceBoundarySignReadout
import N11Formalization.SourceBoundarySignBounds

/-! Actual objective derivative on five independent boundary right-inverse
directions. This module binds the forthcoming interval expressions to fderiv;
no multiplier sign is assumed. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundaryMultiplierFormula
open N11Formalization CartesianReflectionSpace SourceFrameVelocity
open SourceFanLengthCovector
noncomputable section

def testDirection (j : Fin 5) : Frame :=
  BoundaryChartLinear.rightInverse (Pi.single j 1)

theorem testDirection_radius (j : Fin 5) : testDirection j 11=0 := rfl

theorem testDirection_zero :
    testDirection 0 = ![0,0,0,0,-1,0,1,1,1,0,0,0] := by
  ext i
  fin_cases i <;> simp [testDirection,BoundaryChartLinear.rightInverse,
    Pi.single_apply,Fin.reduceFinMk] <;> norm_num

theorem testDirection_one :
    testDirection 1 = ![0,0,0,0,-1,0,0,1,1,0,0,0] := by
  ext i
  fin_cases i <;> simp [testDirection,BoundaryChartLinear.rightInverse,
    Pi.single_apply,Fin.reduceFinMk] <;> norm_num

theorem testDirection_two :
    testDirection 2 = ![0,0,0,0,-1,0,0,0,1,0,0,0] := by
  ext i
  fin_cases i <;> simp [testDirection,BoundaryChartLinear.rightInverse,
    Pi.single_apply,Fin.reduceFinMk] <;> norm_num

theorem testDirection_three :
    testDirection 3 = ![0,0,0,0,-1,0,0,0,0,0,0,0] := by
  ext i
  fin_cases i <;> simp [testDirection,BoundaryChartLinear.rightInverse,
    Pi.single_apply,Fin.reduceFinMk] <;> norm_num

theorem testDirection_four :
    testDirection 4 = ![0,0,0,0,-1/2,1/2,1/2,1/2,1/2,0,0,0] := by
  ext i
  fin_cases i <;> simp [testDirection,BoundaryChartLinear.rightInverse,
    Pi.single_apply,Fin.reduceFinMk] <;> norm_num

theorem frameJac_hubA (v : Frame) : FullCartesianResidual.hubA (frameJac v)=!₂[v 9,0] := by
  ext q
  fin_cases q <;> rfl

theorem frameJac_hubB (v : Frame) : FullCartesianResidual.hubB (frameJac v)=!₂[v 10,0] := by
  ext q
  fin_cases q <;> rfl

theorem testDirection_hubs (j : Fin 5) :
    FullCartesianResidual.hubA (frameJac (testDirection j))=0 ∧
    FullCartesianResidual.hubB (frameJac (testDirection j))=0 := by
  rw [frameJac_hubA,frameJac_hubB]
  constructor <;> ext q <;> fin_cases q <;> rfl

def fanNumerator (k : Fin 9) (j : Fin 5) : ℝ :=
  sourceA k*inner ℝ (normalP k) (velocity k (testDirection j))+
  sourceB k*inner ℝ (normalQ k) (velocity (k+1) (testDirection j))

def numerator (j : Fin 5) : ℝ :=
  -(last5 SourceExactRoot.sourceRoot 0*fanNumerator 1 j+
    last5 SourceExactRoot.sourceRoot 1*fanNumerator 2 j+
    last5 SourceExactRoot.sourceRoot 2*fanNumerator 3 j+
    last5 SourceExactRoot.sourceRoot 3*fanNumerator 8 j)+
    last5 SourceExactRoot.sourceRoot 4*
      inner ℝ SourceCentralGeometry.nH (velocity 6 (testDirection j))

theorem testDirection_multiplier (j : Fin 5) :
    fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint
      (testDirection j)=PhysicalBoundaryStationarity.boundaryMultiplier j := by
  have h := TrueResidualFrame.objectiveTrue_boundary_dual (testDirection j)
  change fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint
    (testDirection j)=_ at h
  rw [show BoundaryChartLinear.boundary (testDirection j)=Pi.single j 1 from
    BoundaryChartLinear.boundary_rightInverse _] at h
  change fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint
      (testDirection j) =
    BoundaryChartDual.multiplier
      (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
        CoupledRadialFrame.sourcePoint (Pi.single i 1)) j
  have hsum :
      (∑ j₁ : Fin 5,
        BoundaryChartDual.multiplier
            (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
              CoupledRadialFrame.sourcePoint (Pi.single i 1)) j₁ *
          ((Pi.single j (1 : ℝ) : Fin 5 → ℝ) j₁)) =
        BoundaryChartDual.multiplier
          (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
            CoupledRadialFrame.sourcePoint (Pi.single i 1)) j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  change fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint
      (testDirection j) =
    BoundaryChartDual.multiplier
      (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
        CoupledRadialFrame.sourcePoint (Pi.single i 1)) j
  exact h.trans hsum

theorem testDirection_fan_derivative (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) (j : Fin 5) :
    fderiv ℝ (fanLength k) FullCartesianResidual.sourcePoint
      (frameJac (testDirection j))=fanNumerator k j/SourceExactRoot.sourceRoot 6 := by
  rw [fanLength_source_fderiv k hk]
  have hh := testDirection_hubs j
  have hH : fullHub k (frameJac (testDirection j))=0 := by
    unfold fullHub
    split_ifs <;> [exact hh.2; exact hh.1]
  simp only [SourceFanRadiusDerivative.left_ringData,
    SourceFanRadiusDerivative.right_ringData,ring_frameJac,hH,inner_zero_right,
    frameJac_radius,testDirection_radius,mul_zero,zero_div,sub_zero,add_zero]
  unfold fanNumerator
  ring

theorem testDirection_central_derivative (j : Fin 5) :
    fderiv ℝ SourceCentralDerivative.centralLength FullCartesianResidual.sourcePoint
      (frameJac (testDirection j))=
      -inner ℝ SourceCentralGeometry.nH (velocity 6 (testDirection j))/
        SourceExactRoot.sourceRoot 6 := by
  rw [SourceCentralDerivative.centralLength_fderiv]
  obtain ⟨hA,hB⟩ := testDirection_hubs j
  simp only [hA,hB,inner_zero_right,mul_zero,zero_div,zero_add,ring_frameJac,
    frameJac_radius,testDirection_radius,add_zero,zero_sub]
  simp only [SourceCentralGeometry.R]
  ring

/-- All five actual multipliers equal the explicit true-length expressions.
Every derivative, chart-stationarity and source-branch premise is paid. -/
theorem multiplier_numerator (j : Fin 5) :
    PhysicalBoundaryStationarity.boundaryMultiplier j=
      numerator j/SourceExactRoot.sourceRoot 6 := by
  have hD := FullCartesianDual.fullDerivative_frame (testDirection j)
  have hObj :
      FullCartesianDual.fullDerivative (frameJac (testDirection j))=
      (frameJac (testDirection j)) 22-
      ∑ k : Fin 5,last5 SourceExactRoot.sourceRoot k*
        fderiv ℝ (fun x : Full => FullCartesianResidual.residualFull x k)
          FullCartesianResidual.sourcePoint (frameJac (testDirection j)) := by
    have hf := PhysicalInteriorObjective.physicalDerivative_eq_length
    rw [← hf]
    simp only [PhysicalInteriorObjective.physicalDerivative,add_apply,
      ContinuousLinearMap.sum_apply,smul_apply,smul_eq_mul,
      ContinuousLinearMap.proj_apply,PhysicalInteriorObjective.weight]
    simp_rw [PhysicalInteriorObjective.length_row_conversion]
    apply congrArg (fun t => frameJac (testDirection j) 22 + t)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  change FullCartesianDual.fullDerivative (frameJac (testDirection j)) =
    fderiv ℝ TrueResidualFrame.objectiveTrue CoupledRadialFrame.sourcePoint
      (testDirection j) at hD
  rw [hObj,testDirection_multiplier,frameJac_radius,testDirection_radius] at hD
  have hrow (k : Fin 5) :
      fderiv ℝ (fun x : Full => FullCartesianResidual.residualFull x k)
        FullCartesianResidual.sourcePoint (frameJac (testDirection j))=
      ![fanNumerator 1 j/SourceExactRoot.sourceRoot 6,
        fanNumerator 2 j/SourceExactRoot.sourceRoot 6,
        fanNumerator 3 j/SourceExactRoot.sourceRoot 6,
        fanNumerator 8 j/SourceExactRoot.sourceRoot 6,
        -inner ℝ SourceCentralGeometry.nH (velocity 6 (testDirection j))/
          SourceExactRoot.sourceRoot 6] k := by
    fin_cases k
    · exact testDirection_fan_derivative 1 (by simp) j
    · exact testDirection_fan_derivative 2 (by simp) j
    · exact testDirection_fan_derivative 3 (by simp) j
    · exact testDirection_fan_derivative 8 (by simp) j
    · exact testDirection_central_derivative j
  rw [← hD]
  simp_rw [hrow]
  simp [Fin.sum_univ_succ,last5,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Fin.reduceFinMk]
  unfold numerator
  have hl0 : last5 SourceExactRoot.sourceRoot 0 = SourceExactRoot.sourceRoot 7 := rfl
  have hl1 : last5 SourceExactRoot.sourceRoot 1 = SourceExactRoot.sourceRoot 8 := rfl
  have hl2 : last5 SourceExactRoot.sourceRoot 2 = SourceExactRoot.sourceRoot 9 := rfl
  have hl3 : last5 SourceExactRoot.sourceRoot 3 = SourceExactRoot.sourceRoot 10 := rfl
  have hl4 : last5 SourceExactRoot.sourceRoot 4 = SourceExactRoot.sourceRoot 11 := rfl
  rw [hl0,hl1,hl2,hl3,hl4]
  ring

end
end N11Formalization.SourceBoundaryMultiplierFormula
#check @N11Formalization.SourceBoundaryMultiplierFormula.multiplier_numerator
#print axioms N11Formalization.SourceBoundaryMultiplierFormula.multiplier_numerator
