import N11Formalization.CoupledRadialFrame
import N11Formalization.PhysicalFrameSmooth
set_option autoImplicit false
namespace N11Formalization.RootRadialDualConsumer
open N11Formalization CoupledRadialFrame PhysicalResidualFrame BoundaryChartSource
noncomputable section

/-- The actual source objective expressed in independent rho/direction/hub/R coordinates.
This uses the certified local inverse; it is not yet a Cartesian center objective. -/
def objectiveRho (y : Frame) : ℝ :=
  objectiveFrame SourceExactRoot.sourceRoot (sourceInverse y)

/-- Full local source-function identity, not merely agreement of derivatives at one point. -/
theorem objectiveRho_radial_eventually :
    ∀ᶠ x in nhds sourcePoint,
      objectiveRho (radialFrame x) = objectiveFrame SourceExactRoot.sourceRoot x := by
  filter_upwards [sourceInverse_left] with x hx
  simp only [objectiveRho, hx]

/-- Radius is an independent coordinate of this inverse, not implicitly held constant. -/
theorem sourceInverse_radius_eventually :
    ∀ᶠ y in nhds (radialFrame sourcePoint), sourceInverse y 11 = y 11 := by
  filter_upwards [sourceInverse_right] with y hy
  have h := congrFun hy 11
  simpa only [radialFrame, show ¬ ((11 : Fin 12) : ℕ) < 5 from by decide, if_false] using h

theorem objectiveRho_hasFDerivAt :
    HasFDerivAt objectiveRho
      ((fderiv ℝ (objectiveFrame SourceExactRoot.sourceRoot) sourcePoint).comp
        (sourceJacobian.symm : Frame →L[ℝ] Frame))
      (radialFrame sourcePoint) := by
  have ho := PhysicalFrameSmooth.sourceRoot_objective_differentiable.hasFDerivAt
  have hi := sourceInverse_strict_derivative.hasFDerivAt
  have ho' : HasFDerivAt (objectiveFrame SourceExactRoot.sourceRoot)
      (fderiv ℝ (objectiveFrame SourceExactRoot.sourceRoot) sourcePoint)
      (sourceInverse (radialFrame sourcePoint)) := by
    rw [sourceInverse_apply_image]
    exact ho
  exact ho'.comp (radialFrame sourcePoint) hi

/-- Unconditional source covector transport, including the variable-radius inverse column.
The five boundary covectors are pulled back rather than identified with source stress. -/
theorem sourceRoot_rho_dual (v : Frame) :
    fderiv ℝ objectiveRho (radialFrame sourcePoint) v =
      ∑ j : Fin 5,
        BoundaryChartDual.multiplier (fun i =>
          fderiv ℝ (objectiveFrame SourceExactRoot.sourceRoot) sourcePoint (Pi.single i 1)) j *
        BoundaryChartLinear.boundary
          (triangularInv (slopeA sourcePoint) (slopeB sourcePoint) v) j := by
  rw [objectiveRho_hasFDerivAt.fderiv]
  change fderiv ℝ (objectiveFrame SourceExactRoot.sourceRoot) sourcePoint
    (sourceJacobian.symm v) = _
  rw [sourceJacobian_symm_apply]
  exact PhysicalFrameSmooth.sourceRoot_objective_dual _

end
end N11Formalization.RootRadialDualConsumer
#check @N11Formalization.RootRadialDualConsumer.objectiveRho_hasFDerivAt
#check @N11Formalization.RootRadialDualConsumer.sourceRoot_rho_dual
#print axioms N11Formalization.RootRadialDualConsumer.sourceRoot_rho_dual
