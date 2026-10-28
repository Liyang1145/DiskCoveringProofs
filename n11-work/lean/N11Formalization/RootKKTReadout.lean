import Mathlib
import N11Formalization.TCChartStationarityRoot
set_option autoImplicit false
namespace N11Formalization.RootKKTReadout
open N11Formalization
open N11Formalization.TCChartStationarity
noncomputable section

/-- The chart stationarity at the exact source root reads the KKT adjoint block
as the radius-coordinate covector.  This is the explicit coordinate form of the
already proved objective stationarity; it is not yet a geometric B2-force identity. -/
theorem sourceRoot_adjointBlock_unit :
    adjointBlock (first7 SourceExactRoot.sourceRoot) (last5 SourceExactRoot.sourceRoot) =
      fun i : Fin 7 => if i = 6 then (1 : ℝ) else 0 := by
  funext i
  have hzero : objectiveDeriv SourceExactRoot.sourceRoot = 0 :=
    objectiveDeriv_zero_of_TC SourceExactRoot.sourceRoot SourceExactRoot.sourceRoot_mem.2
  have h := congrArg
    (fun L : (Fin 7 → ℝ) →L[ℝ] ℝ => L (Pi.single i (1 : ℝ))) hzero
  rw [objectiveDeriv_single] at h
  simp only [zero_apply] at h
  linarith

/-- Component form: every non-radius chart coordinate has zero adjoint value. -/
theorem sourceRoot_adjointBlock_nonradius (i : Fin 7) (hi : i ≠ 6) :
    adjointBlock (first7 SourceExactRoot.sourceRoot) (last5 SourceExactRoot.sourceRoot) i = 0 := by
  rw [sourceRoot_adjointBlock_unit]
  simp [hi]

/-- Component form at the radius coordinate. -/
theorem sourceRoot_adjointBlock_radius :
    adjointBlock (first7 SourceExactRoot.sourceRoot) (last5 SourceExactRoot.sourceRoot) 6 = 1 := by
  rw [sourceRoot_adjointBlock_unit]
  simp

end
end N11Formalization.RootKKTReadout
#print axioms N11Formalization.RootKKTReadout.sourceRoot_adjointBlock_unit
#print axioms N11Formalization.RootKKTReadout.sourceRoot_adjointBlock_radius
