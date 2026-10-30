import N11Formalization.EnergyTerminalBatchB13Main
import N11Formalization.EnergyTerminalBatchB13RefineSeven

/-! Conditional main-thread consumer for the combined seven-certificate B13
refinement.  Only the energy premise changes; the seven-class premise remains
explicit and unpaid. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSevenMain
noncomputable section

theorem main_of_energy_refineSeven_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineSeven.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13RefineSeven.remaining_of henergy) hclasses

theorem full_disk_bound_of_energy_refineSeven_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineSeven.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_energy_refineSeven_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13RefineSevenMain
#check @N11Formalization.EnergyTerminalBatchB13RefineSevenMain.main_of_energy_refineSeven_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSevenMain.full_disk_bound_of_energy_refineSeven_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSevenMain.main_of_energy_refineSeven_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSevenMain.full_disk_bound_of_energy_refineSeven_and_seven_classes
