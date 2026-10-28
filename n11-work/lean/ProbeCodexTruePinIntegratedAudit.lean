import N11Formalization
set_option autoImplicit false

-- Full source identities and Cartesian-coordinate definitions.
#print N11Formalization.SourceExactRoot.sourceRoot
#print N11Formalization.SourceExactRoot.sourceRadius
#print N11Formalization.TrueCirclePinSmooth.Data
#print N11Formalization.TrueCirclePinSmooth.left
#print N11Formalization.TrueCirclePinSmooth.right
#print N11Formalization.TrueCirclePinSmooth.sourceData
#print N11Formalization.TrueCirclePinSmooth.sourceSeed
#print N11Formalization.TruePinFrameDifferential.frameData
#print N11Formalization.TruePinFrameDifferential.framePin
#print N11Formalization.TrueResidualFrame.residualTrue
#print N11Formalization.TrueResidualFrame.objectiveTrue

-- Actual construction and all remaining premises.
#check @N11Formalization.TrueCirclePin.pin_circle_equations
#check @N11Formalization.TrueCirclePinSmooth.source_pinData_eq
#check @N11Formalization.TrueCirclePinSmooth.source_pinData_smooth
#check @N11Formalization.TrueCirclePinSmooth.source_pinData_equations_eventually
#check @N11Formalization.TruePinChartConsumer.truePin_source_fderiv
#check @N11Formalization.TruePinFrameDifferential.framePin_source_smooth
#check @N11Formalization.TruePinFrameDifferential.framePin_chart_derivative
#check @N11Formalization.TruePinFrameDifferential.discrepancy_kernel_zero
#check @N11Formalization.TruePinFrameDifferential.discrepancy_boundary_factorization
#check @N11Formalization.TrueResidualFrame.residualTrue_source
#check @N11Formalization.TrueResidualFrame.residualTrue_source_smooth
#check @N11Formalization.TrueResidualFrame.residualTrue_chart_derivative
#check @N11Formalization.TrueResidualFrame.objectiveTrue_chart_stationarity
#check @N11Formalization.TrueResidualFrame.objectiveTrue_boundary_dual
#check @N11Formalization.TruePinCartesianDifferential.source_cartesian_normal_rows
#check @N11Formalization.TruePinCartesianDifferential.source_cartesian_covector_elimination

-- Preserve the completed attainment and expose, rather than hide, the unpaid global bound.
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound

#print axioms N11Formalization.TrueCirclePin.pin_circle_equations
#print axioms N11Formalization.TrueCirclePinSmooth.source_pinData_eq
#print axioms N11Formalization.TrueCirclePinSmooth.source_pinData_smooth
#print axioms N11Formalization.TrueCirclePinSmooth.source_pinData_equations_eventually
#print axioms N11Formalization.TruePinChartConsumer.truePin_source_fderiv
#print axioms N11Formalization.TruePinFrameDifferential.discrepancy_boundary_factorization
#print axioms N11Formalization.TrueResidualFrame.residualTrue_chart_derivative
#print axioms N11Formalization.TrueResidualFrame.objectiveTrue_chart_stationarity
#print axioms N11Formalization.TrueResidualFrame.objectiveTrue_boundary_dual
#print axioms N11Formalization.TruePinCartesianDifferential.source_cartesian_normal_rows
#print axioms N11Formalization.TruePinCartesianDifferential.source_cartesian_covector_elimination
#print axioms N11Formalization.SourceExactRoot.source_attainment
#print axioms N11Formalization.SourceExactRoot.main_of_lower_bound

-- Actual downstream application checks; no theorem-shaped placeholder premises.
example (v : N11Formalization.TruePinFrameDifferential.Frame) :
    fderiv ℝ N11Formalization.TrueResidualFrame.objectiveTrue
      N11Formalization.TruePinFrameDifferential.sourcePoint v =
    ∑ j : Fin 5, N11Formalization.BoundaryChartDual.multiplier
      (fun i => fderiv ℝ N11Formalization.TrueResidualFrame.objectiveTrue
        N11Formalization.TruePinFrameDifferential.sourcePoint (Pi.single i 1)) j *
      N11Formalization.BoundaryChartLinear.boundary v j :=
  N11Formalization.TrueResidualFrame.objectiveTrue_boundary_dual v

example (dz : N11Formalization.TrueCirclePinSmooth.Data) :
    inner ℝ
      (N11Formalization.Uvec N11Formalization.SourceExactRoot.sourceRoot 8 -
        N11Formalization.ringCenter N11Formalization.SourceExactRoot.sourceRoot 8)
      (N11Formalization.TruePinCartesianDifferential.sourceVelocity 8 dz -
        N11Formalization.TrueCirclePinSmooth.left dz) =
      N11Formalization.SourceExactRoot.sourceRoot 6 * dz 4 :=
  (N11Formalization.TruePinCartesianDifferential.source_cartesian_normal_rows
    8 (by simp) dz).1
