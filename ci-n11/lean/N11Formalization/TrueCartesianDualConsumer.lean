import N11Formalization.CartesianPolarFrame
import N11Formalization.TrueRadialDualConsumer

/-!
TRUE length objective in independent reflection-fixed Cartesian coordinates.
The Cartesian/polar local inverse is explicit and includes all four ring-pair
polar blocks, hubs, central-ring coordinate and radius. The resulting dual is
still on the reflection-fixed 12D space; the full 23D orbit lift and B2 force
identification remain downstream obligations.
-/
set_option autoImplicit false
namespace N11Formalization.TrueCartesianDualConsumer
open N11Formalization CartesianPolarFrame CoupledRadialFrame
noncomputable section

def objectiveCartesian (q : Frame) : ℝ :=
  TrueRadialDualConsumer.objectiveRho (CartesianPolarFrame.sourceInverse q)

theorem objectiveCartesian_hasFDerivAt :
    HasFDerivAt objectiveCartesian
      (((fderiv ℝ TrueResidualFrame.objectiveTrue
        CoupledRadialFrame.sourcePoint).comp
          (CoupledRadialFrame.sourceJacobian.symm : Frame →L[ℝ] Frame)).comp
        (CartesianPolarFrame.sourceJacobian.symm : Frame →L[ℝ] Frame))
      (CartesianPolarFrame.cartesian CartesianPolarFrame.sourceRho) := by
  have ho0 := TrueRadialDualConsumer.objectiveRho_hasFDerivAt
  have ho : HasFDerivAt TrueRadialDualConsumer.objectiveRho
      ((fderiv ℝ TrueResidualFrame.objectiveTrue
        CoupledRadialFrame.sourcePoint).comp
        (CoupledRadialFrame.sourceJacobian.symm : Frame →L[ℝ] Frame))
      CartesianPolarFrame.sourceRho := by
    simpa only [CartesianPolarFrame.sourceRho] using ho0
  change HasFDerivAt TrueRadialDualConsumer.objectiveRho
      ((fderiv ℝ TrueResidualFrame.objectiveTrue
        CoupledRadialFrame.sourcePoint).comp
        (CoupledRadialFrame.sourceJacobian.symm : Frame →L[ℝ] Frame))
      (radialFrame CoupledRadialFrame.sourcePoint) at ho
  have hi := CartesianPolarFrame.sourceInverse_strict_derivative.hasFDerivAt
  have hsrc := CartesianPolarFrame.sourceInverse_apply_image
  have ho' : HasFDerivAt TrueRadialDualConsumer.objectiveRho
      ((fderiv ℝ TrueResidualFrame.objectiveTrue
        CoupledRadialFrame.sourcePoint).comp
        (CoupledRadialFrame.sourceJacobian.symm : Frame →L[ℝ] Frame))
      (CartesianPolarFrame.sourceInverse
        (CartesianPolarFrame.cartesian CartesianPolarFrame.sourceRho)) := by
    rw [hsrc]
    exact ho
  exact ho'.comp (CartesianPolarFrame.cartesian CartesianPolarFrame.sourceRho) hi

theorem sourceRoot_true_cartesian_dual (v : Frame) :
    fderiv ℝ objectiveCartesian
      (CartesianPolarFrame.cartesian CartesianPolarFrame.sourceRho) v =
      ∑ j : Fin 5,
        BoundaryChartDual.multiplier
          (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
            CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
        BoundaryChartLinear.boundary
          (CoupledRadialFrame.triangularInv
            (CoupledRadialFrame.slopeA CoupledRadialFrame.sourcePoint)
            (CoupledRadialFrame.slopeB CoupledRadialFrame.sourcePoint)
            (CartesianPolarFrame.sourceJacobian.symm v)) j := by
  rw [objectiveCartesian_hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have hdual := TrueRadialDualConsumer.sourceRoot_true_rho_dual
    (CartesianPolarFrame.sourceJacobian.symm v)
  rw [TrueRadialDualConsumer.objectiveRho_hasFDerivAt.fderiv] at hdual
  exact hdual

end
end N11Formalization.TrueCartesianDualConsumer
#check @N11Formalization.TrueCartesianDualConsumer.sourceRoot_true_cartesian_dual
#print axioms N11Formalization.TrueCartesianDualConsumer.sourceRoot_true_cartesian_dual
