import N11Formalization.C450ChainCompletionMain
import N11Formalization.EnergyTerminalBatchB13
import N11Formalization.ActualMetricClassReduction

/-! The conditional main statement with the energy premise weakened from
`EnergyTerminalBatchB12.RemainingTerminalRadius` (1571 terminals) to
`EnergyTerminalBatchB13.RemainingTerminalRadius` (389 terminals). -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13Main
noncomputable section

theorem main_of_energy_b13_and_seven_classes
    (henergy : EnergyTerminalBatchB13.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  C450ChainCompletionMain.main_of_energy_and_seven_classes
    (EnergyTerminalBatchB13.remaining_of_b13 henergy) hclasses

theorem full_disk_bound_of_energy_b13_and_seven_classes
    (henergy : EnergyTerminalBatchB13.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main (main_of_energy_b13_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13Main
#check @N11Formalization.EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
