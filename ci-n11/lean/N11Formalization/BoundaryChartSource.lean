import Mathlib
import N11Formalization.TCSystem
import N11Formalization.BoundaryChartLinear
set_option autoImplicit false
namespace N11Formalization.BoundaryChartSource
open N11Formalization.BoundaryChartLinear
noncomputable section

/-- Actual TC source width-direction data; no radial branch assertions. -/
def sourceFrame (u : Fin 12 → ℝ) : Fin 12 → ℝ :=
  ![angleVec u 0, angleVec u 1, angleVec u 2, angleVec u 3, angleVec u 4,
    thetaOf (angleVec u) 0, thetaOf (angleVec u) 1,
    thetaOf (angleVec u) 2, thetaOf (angleVec u) 3, u 4, u 5, u 6]

theorem sourceFrame_eq_affineChart (u : Fin 12 → ℝ) :
    sourceFrame u = affineChart (first7 u) := by
  funext i
  fin_cases i <;> simp [sourceFrame, affineChart, first7, angleVec, thetaOf, Fin.reduceFinMk] <;> ring

/-- The real source chart satisfies all five reflection-orbit boundary equations exactly. -/
theorem sourceFrame_boundary_zero (u : Fin 12 → ℝ) :
    affineBoundary (sourceFrame u) = 0 := by
  rw [sourceFrame_eq_affineChart]
  exact affineBoundary_affineChart (first7 u)

/-- The chart coordinates read from this frame are exactly the source first seven coordinates. -/
theorem sourceFrame_extract (u : Fin 12 → ℝ) : extract (sourceFrame u) = first7 u := by
  funext i
  fin_cases i <;> simp [sourceFrame, extract, first7, angleVec, Fin.reduceFinMk]

end
end N11Formalization.BoundaryChartSource
#print axioms N11Formalization.BoundaryChartSource.sourceFrame_eq_affineChart
#print axioms N11Formalization.BoundaryChartSource.sourceFrame_boundary_zero
#check @N11Formalization.BoundaryChartSource.sourceFrame_eq_affineChart
