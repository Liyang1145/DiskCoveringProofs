import Mathlib
import N11Formalization.TCChartStationarity
import N11Formalization.F1.BallD35C13
import N11Formalization.BoxRstar
import N11Formalization.SourceExactRoot
set_option autoImplicit false
namespace N11Formalization.TCChartStationarityRoot
noncomputable section

theorem sourceRoot_mem_ball :
    SourceExactRoot.sourceRoot ∈ Metric.closedBall certCR rhoCertR :=
  mem_closedBall_cert_iff.mpr SourceExactRoot.sourceRoot_mem.1

theorem sourceRoot_residual_differentiable :
    DifferentiableAt ℝ residualFun (first7 SourceExactRoot.sourceRoot) :=
  differentiableAt_residualFun_first7_ball sourceRoot_mem_ball

/-- The actual source root satisfies chart-space objective stationarity with no hd premise. -/
theorem sourceRoot_stationarity :
    fderiv ℝ (TCChartStationarity.objective SourceExactRoot.sourceRoot)
      (first7 SourceExactRoot.sourceRoot) = 0 :=
  TCChartStationarity.sourceRoot_stationarity sourceRoot_residual_differentiable

end
end N11Formalization.TCChartStationarityRoot
#print axioms N11Formalization.TCChartStationarityRoot.sourceRoot_residual_differentiable
#print axioms N11Formalization.TCChartStationarityRoot.sourceRoot_stationarity
#check @N11Formalization.TCChartStationarityRoot.sourceRoot_stationarity
