import Mathlib
import N11Formalization.BoundaryChartLinear
import N11Formalization.BoundaryChartDual
set_option autoImplicit false
namespace N11Formalization.BoundaryChartDifferential
open N11Formalization.BoundaryChartLinear
noncomputable section

def chartLinear : (Fin 7 → ℝ) →ₗ[ℝ] (Fin 12 → ℝ) where
  toFun := chart
  map_add' := by
    intro z w
    funext i
    fin_cases i <;> simp [chart] <;> ring
  map_smul' := by
    intro r z
    funext i
    fin_cases i <;> simp [chart, smul_eq_mul] <;> ring

def chartCLM : (Fin 7 → ℝ) →L[ℝ] (Fin 12 → ℝ) :=
  chartLinear.toContinuousLinearMap

@[simp] theorem chartCLM_apply (z : Fin 7 → ℝ) : chartCLM z = chart z := rfl

theorem affineChart_eq (z : Fin 7 → ℝ) :
    affineChart z = chartCLM z + affineChart 0 := by
  funext i
  fin_cases i <;> simp [chartCLM_apply, affineChart, chart] <;> ring

theorem hasFDerivAt_affineChart (z : Fin 7 → ℝ) :
    HasFDerivAt affineChart chartCLM z := by
  have h : affineChart = fun w => chartCLM w + affineChart 0 := funext affineChart_eq
  rw [h]
  exact chartCLM.hasFDerivAt.add_const _

/-- Consumer: physical objective chart-stationarity transports to the unique boundary dual.
The objective is a genuine nonlinear function; only the INNER affine chart is linear. -/
theorem chart_stationarity_dual {f : (Fin 12 → ℝ) → ℝ}
    {z : Fin 7 → ℝ} {df : (Fin 12 → ℝ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f df (affineChart z))
    (hstat : fderiv ℝ (fun w => f (affineChart w)) z = 0) :
    ∀ x : Fin 12 → ℝ,
      df x = ∑ j : Fin 5,
        N11Formalization.BoundaryChartDual.multiplier
          (fun i => df (Pi.single i 1)) j * boundary x j := by
  have hcomp := hf.comp z (hasFDerivAt_affineChart z)
  have hzero : df.comp chartCLM = 0 := hcomp.fderiv.symm.trans hstat
  have hchart : ∀ w : Fin 7 → ℝ, df (chart w) = 0 := by
    intro w
    have hw := congrArg (fun g : (Fin 7 → ℝ) →L[ℝ] ℝ => g w) hzero
    simpa [ContinuousLinearMap.comp_apply] using hw
  have hcoord : ∀ x : Fin 12 → ℝ,
      df x = ∑ i : Fin 12, df (Pi.single i 1) * x i := by
    intro x
    have hx : x = ∑ i : Fin 12, (x i) • (Pi.single i (1 : ℝ)) := by
      funext j
      simp [Pi.single_apply]
    calc
      df x = df (∑ i : Fin 12, (x i) • (Pi.single i (1 : ℝ))) := congrArg df hx
      _ = ∑ i : Fin 12, df (Pi.single i 1) * x i := by
        simp [map_sum, mul_comm]
  have hsum : ∀ w : Fin 7 → ℝ,
      ∑ i, df (Pi.single i 1) * chart w i = 0 := by
    intro w
    rw [← hcoord, hchart]
  intro x
  rw [hcoord]
  exact N11Formalization.BoundaryChartDual.factor_through_boundary
    (fun i => df (Pi.single i 1)) hsum x

end
end N11Formalization.BoundaryChartDifferential
#print axioms N11Formalization.BoundaryChartDifferential.hasFDerivAt_affineChart
#print axioms N11Formalization.BoundaryChartDifferential.chart_stationarity_dual
#check @N11Formalization.BoundaryChartDifferential.chart_stationarity_dual
