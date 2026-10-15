import N11Formalization
set_option autoImplicit false
open N11Formalization

#check @N11Formalization.TrueRadialDualConsumer.residualRho_radial_eventually
#check @N11Formalization.TrueRadialDualConsumer.objectiveRho_radial_eventually
#check @N11Formalization.TrueRadialDualConsumer.objectiveRho_formula_eventually
#check @N11Formalization.TrueRadialDualConsumer.objectiveRho_hasFDerivAt
#check @N11Formalization.TrueRadialDualConsumer.sourceRoot_true_rho_dual
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound

#print axioms N11Formalization.TrueRadialDualConsumer.objectiveRho_hasFDerivAt
#print axioms N11Formalization.TrueRadialDualConsumer.sourceRoot_true_rho_dual
#print axioms N11Formalization.SourceExactRoot.main_of_lower_bound

example (v : N11Formalization.CoupledRadialFrame.Frame) :
    fderiv ℝ N11Formalization.TrueRadialDualConsumer.objectiveRho
      (N11Formalization.CoupledRadialFrame.radialFrame
        N11Formalization.CoupledRadialFrame.sourcePoint) v =
    ∑ j : Fin 5,
      N11Formalization.BoundaryChartDual.multiplier
        (fun i => fderiv ℝ N11Formalization.TrueResidualFrame.objectiveTrue
          N11Formalization.CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
      N11Formalization.BoundaryChartLinear.boundary
        (N11Formalization.CoupledRadialFrame.triangularInv
          (N11Formalization.CoupledRadialFrame.slopeA
            N11Formalization.CoupledRadialFrame.sourcePoint)
          (N11Formalization.CoupledRadialFrame.slopeB
            N11Formalization.CoupledRadialFrame.sourcePoint) v) j :=
  N11Formalization.TrueRadialDualConsumer.sourceRoot_true_rho_dual v
