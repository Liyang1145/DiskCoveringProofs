import N11Formalization.EnergyTerminalBatchB13Main
import N11Formalization.EnergyTerminalBatchB13RefineEight

/-! Conditional main-thread consumer for the eight-certificate B13 refinement. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineEightMain
noncomputable section

theorem main_of_energy_refineEight_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineEight.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13RefineEight.remaining_of henergy) hclasses

theorem full_disk_bound_of_energy_refineEight_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineEight.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_energy_refineEight_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13RefineEightMain
