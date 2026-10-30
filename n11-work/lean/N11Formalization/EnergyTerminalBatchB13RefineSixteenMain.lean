import N11Formalization.EnergyTerminalBatchB13Main
import N11Formalization.EnergyTerminalBatchB13RefineSixteen

/-! Conditional main-thread consumer for the sixteen-certificate B13
refinement.  The seven-class premise remains explicit. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenMain
noncomputable section

theorem main_of_energy_refineSixteen_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineSixteen.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13RefineSixteen.remaining_of henergy) hclasses

theorem full_disk_bound_of_energy_refineSixteen_and_seven_classes
    (henergy : EnergyTerminalBatchB13RefineSixteen.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_energy_refineSixteen_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenMain
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenMain.main_of_energy_refineSixteen_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenMain.full_disk_bound_of_energy_refineSixteen_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenMain.main_of_energy_refineSixteen_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenMain.full_disk_bound_of_energy_refineSixteen_and_seven_classes
