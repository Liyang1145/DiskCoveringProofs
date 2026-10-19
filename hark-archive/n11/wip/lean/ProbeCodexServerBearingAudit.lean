import N11Formalization
set_option autoImplicit false
open N11Formalization

#check @TrueCirclePin.pin_circle_equations
#check @TrueCirclePinSmooth.source_pinData_eq
#check @TrueCirclePinSmooth.source_pinData_smooth
#check @TrueCirclePinSmooth.source_pinData_equations_eventually
#check @TruePinChartConsumer.truePin_source_fderiv
#check @TruePinFrameDifferential.discrepancy_boundary_factorization
#check @FullCartesianDual.actual_full_cartesian_dual
#check @SourceCentreB2Readout.all_B2_rows
#check @SourceCentreB2Readout.canonical_free_balance
#check @SourceBoundaryStressPositive.stress_pos
#check @SourceActiveHarmonicSolve.activeH_solve
#check @SourceActiveAffineResponse.actual_pair_le_oracle
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment

#print TrueCirclePinSmooth.Data
#print TruePinChartConsumer.dataOf
#print SourceExactRoot.sourceRadius
#print axioms TrueCirclePinSmooth.source_pinData_equations_eventually
#print axioms TruePinChartConsumer.truePin_source_fderiv
#print axioms TruePinFrameDifferential.discrepancy_boundary_factorization
#print axioms FullCartesianDual.actual_full_cartesian_dual
#print axioms SourceCentreB2Readout.all_B2_rows
#print axioms SourceBoundaryStressPositive.stress_pos
#print axioms SourceActiveAffineResponse.actual_pair_le_oracle
#print axioms SourceExactRoot.source_attainment

example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl

example (k : Fin 9) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 8) :
    fderiv ℝ (TruePinChartConsumer.truePin k) SourceExactRoot.sourceRoot =
      fderiv ℝ (fun u : RootPinCurveSmooth.TCPoint => Uvec u k) SourceExactRoot.sourceRoot :=
  TruePinChartConsumer.truePin_source_fderiv k hk

example (w : HarmonicSourceTransport.SrcFree) (c : Fin 2) :
    ∑ e : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot
        (HarmonicSourceGeometryV2.rowIdx w c) (HarmonicSourceTransport.srcFlat e) *
          SourceSignedStressAssembly.stress e = 0 :=
  SourceCentreB2Readout.all_B2_rows w c

-- Both real hub rows: no Fin9 wraparound surrogate is used.
example (c : Fin 2) :
    ∑ e : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot (⟨18 + c.val, by omega⟩ : Fin 41)
        (HarmonicSourceTransport.srcFlat e) * SourceSignedStressAssembly.stress e = 0 :=
  SourceCentreB2Readout.full_centre_B2_rows 9 c

example (c : Fin 2) :
    ∑ e : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot (⟨20 + c.val, by omega⟩ : Fin 41)
        (HarmonicSourceTransport.srcFlat e) * SourceSignedStressAssembly.stress e = 0 :=
  SourceCentreB2Readout.full_centre_B2_rows 10 c

example (θ : Fin 9 → ℝ) :
    (2 * ∑ i : Fin 9, ∑ j : Fin 9, if i < j then
      -SourceResponseFluxIdentity.sourceResponse i j *
        (1 - Real.cos (θ i - θ j)) else 0) ≤
          ResumeNetwork.V2 (fun j => circleMap (θ j)) :=
  SourceActiveAffineResponse.actual_pair_le_oracle θ
