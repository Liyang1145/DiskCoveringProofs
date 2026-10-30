import N11Formalization.EnergyTerminalBatchB13Main
import N11Formalization.EnergyTerminalBatchB13RefineTwelve

/-! Conditional main-thread consumer for the twelve-certificate B13 refinement. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineTwelveMain
noncomputable section

theorem main_of_energy_refineTwelve_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineTwelve.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13RefineTwelve.remaining_of henergy) hclasses

theorem full_disk_bound_of_energy_refineTwelve_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineTwelve.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_energy_refineTwelve_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13RefineTwelveMain
#check @N11Formalization.EnergyTerminalBatchB13RefineTwelveMain.main_of_energy_refineTwelve_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineTwelveMain.main_of_energy_refineTwelve_and_seven_classes
