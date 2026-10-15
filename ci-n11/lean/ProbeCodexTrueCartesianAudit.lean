import N11Formalization
set_option autoImplicit false
open N11Formalization

#check @N11Formalization.CartesianPolarFrame.polarBlock_left_inverse
#check @N11Formalization.CartesianPolarFrame.source_strict_derivative
#check @N11Formalization.CartesianPolarFrame.sourceInverse_strict_derivative
#check @N11Formalization.TrueCartesianDualConsumer.objectiveCartesian_hasFDerivAt
#check @N11Formalization.TrueCartesianDualConsumer.sourceRoot_true_cartesian_dual

#print axioms N11Formalization.CartesianPolarFrame.source_strict_derivative
#print axioms N11Formalization.CartesianPolarFrame.sourceInverse_strict_derivative
#print axioms N11Formalization.TrueCartesianDualConsumer.sourceRoot_true_cartesian_dual

example (v : N11Formalization.CoupledRadialFrame.Frame) :
    fderiv ℝ N11Formalization.TrueCartesianDualConsumer.objectiveCartesian
      (N11Formalization.CartesianPolarFrame.cartesian
        N11Formalization.CartesianPolarFrame.sourceRho) v =
    ∑ j : Fin 5,
      N11Formalization.BoundaryChartDual.multiplier
        (fun i => fderiv ℝ N11Formalization.TrueResidualFrame.objectiveTrue
          N11Formalization.CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
      N11Formalization.BoundaryChartLinear.boundary
        (N11Formalization.CoupledRadialFrame.triangularInv
          (N11Formalization.CoupledRadialFrame.slopeA
            N11Formalization.CoupledRadialFrame.sourcePoint)
          (N11Formalization.CoupledRadialFrame.slopeB
            N11Formalization.CoupledRadialFrame.sourcePoint)
          (N11Formalization.CartesianPolarFrame.sourceJacobian.symm v)) j :=
  N11Formalization.TrueCartesianDualConsumer.sourceRoot_true_cartesian_dual v
