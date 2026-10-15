import Mathlib
import N11Formalization.BoundaryChartSource
import N11Formalization.BoundaryChartDifferential
import N11Formalization.SourceExactRoot
set_option autoImplicit false
namespace N11Formalization.RootBoundaryDualConsumer
open N11Formalization
open N11Formalization.BoundaryChartSource
open N11Formalization.BoundaryChartDifferential
open N11Formalization.BoundaryChartLinear
open N11Formalization.BoundaryChartDual
noncomputable section

/-- The exact source frame lies on the affine boundary chart. -/
theorem sourceRoot_frame_eq_chart :
    sourceFrame SourceExactRoot.sourceRoot =
      affineChart (first7 SourceExactRoot.sourceRoot) :=
  sourceFrame_eq_affineChart SourceExactRoot.sourceRoot

/-- Consumer-facing physical dual factorization at the exact source frame.
The physical derivative and its chart stationarity are explicit premises: this theorem
never identifies the TC chart objective with the physical residual objective. -/
theorem physical_dual_factorization
    {f : (Fin 12 → ℝ) → ℝ}
    {df : (Fin 12 → ℝ) →L[ℝ] ℝ}
    (hdf : HasFDerivAt f df (sourceFrame SourceExactRoot.sourceRoot))
    (hstat : fderiv ℝ (fun z : Fin 7 → ℝ =>
        f (affineChart z)) (first7 SourceExactRoot.sourceRoot) = 0) :
    ∀ x : Fin 12 → ℝ,
      df x = ∑ j : Fin 5,
        multiplier (fun i => df (Pi.single i 1)) j *
          boundary x j := by
  apply chart_stationarity_dual (z := first7 SourceExactRoot.sourceRoot)
  · convert hdf using 1
    exact sourceRoot_frame_eq_chart.symm
  · exact hstat

end
end N11Formalization.RootBoundaryDualConsumer
#print axioms N11Formalization.RootBoundaryDualConsumer.physical_dual_factorization
