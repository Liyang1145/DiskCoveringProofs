import N11Formalization.TrueResidualFrame
import N11Formalization.RootRadialDualConsumer

/-!
Genuine equal-circle LENGTH residuals in independent rho/direction/hub/R data.
The certified variable-R inverse is used, including its radius column.
This replaces the reflected off-boundary objective used by the earlier radial
consumer. Cartesian coordinate stationarity and B2 forces are still separate.
-/
set_option autoImplicit false
namespace N11Formalization.TrueRadialDualConsumer
open N11Formalization CoupledRadialFrame
noncomputable section

def residualRho (y : Frame) : Fin 5 → ℝ :=
  TrueResidualFrame.residualTrue (sourceInverse y)

def objectiveRho (y : Frame) : ℝ :=
  TrueResidualFrame.objectiveTrue (sourceInverse y)

theorem residualRho_radial_eventually :
    ∀ᶠ x in nhds sourcePoint,
      residualRho (radialFrame x) = TrueResidualFrame.residualTrue x := by
  filter_upwards [sourceInverse_left] with x hx
  simp only [residualRho, hx]

theorem objectiveRho_radial_eventually :
    ∀ᶠ x in nhds sourcePoint,
      objectiveRho (radialFrame x) = TrueResidualFrame.objectiveTrue x := by
  filter_upwards [sourceInverse_left] with x hx
  simp only [objectiveRho, hx]

/-- The coordinate R is retained as the actual variable-radius coordinate. -/
theorem objectiveRho_formula_eventually :
    ∀ᶠ y in nhds (radialFrame sourcePoint),
      objectiveRho y = y 11 -
        ∑ k : Fin 5, last5 SourceExactRoot.sourceRoot k * residualRho y k := by
  filter_upwards [RootRadialDualConsumer.sourceInverse_radius_eventually] with y hy
  simp only [objectiveRho, TrueResidualFrame.objectiveTrue, residualRho, hy]

theorem objectiveRho_hasFDerivAt :
    HasFDerivAt objectiveRho
      ((fderiv ℝ TrueResidualFrame.objectiveTrue sourcePoint).comp
        (sourceJacobian.symm : Frame →L[ℝ] Frame))
      (radialFrame sourcePoint) := by
  have ho : HasFDerivAt TrueResidualFrame.objectiveTrue
      (fderiv ℝ TrueResidualFrame.objectiveTrue sourcePoint) sourcePoint := by
    simpa only [sourcePoint, TruePinFrameDifferential.sourcePoint] using
      (TrueResidualFrame.objectiveTrue_source_smooth.differentiableAt
        (by norm_num)).hasFDerivAt
  have ho' : HasFDerivAt TrueResidualFrame.objectiveTrue
      (fderiv ℝ TrueResidualFrame.objectiveTrue sourcePoint)
      (sourceInverse (radialFrame sourcePoint)) := by
    rw [sourceInverse_apply_image]
    exact ho
  exact ho'.comp (radialFrame sourcePoint) sourceInverse_strict_derivative.hasFDerivAt

/-- The TRUE objective source covector, including the variable-R inverse column.
No smoothness, inverse, or chart-stationarity premise remains. -/
theorem sourceRoot_true_rho_dual (v : Frame) :
    fderiv ℝ objectiveRho (radialFrame sourcePoint) v =
      ∑ j : Fin 5, BoundaryChartDual.multiplier
        (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue sourcePoint (Pi.single i 1)) j *
        BoundaryChartLinear.boundary
          (triangularInv (slopeA sourcePoint) (slopeB sourcePoint) v) j := by
  rw [objectiveRho_hasFDerivAt.fderiv]
  change fderiv ℝ TrueResidualFrame.objectiveTrue sourcePoint
    (sourceJacobian.symm v) = _
  rw [sourceJacobian_symm_apply]
  simpa only [sourcePoint, TruePinFrameDifferential.sourcePoint] using
    TrueResidualFrame.objectiveTrue_boundary_dual
      (triangularInv (slopeA sourcePoint) (slopeB sourcePoint) v)

end
end N11Formalization.TrueRadialDualConsumer
#check @N11Formalization.TrueRadialDualConsumer.sourceRoot_true_rho_dual
#print axioms N11Formalization.TrueRadialDualConsumer.sourceRoot_true_rho_dual
