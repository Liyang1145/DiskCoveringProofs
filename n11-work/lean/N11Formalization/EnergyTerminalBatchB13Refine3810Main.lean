import N11Formalization.EnergyTerminalBatchB13Main
import N11Formalization.EnergyTerminalBatchB13Refine3810

/-! Conditional main-thread consumer for the B13 refinement by source terminal
3810.  The seven-class premise is unchanged; only the energy premise is
weakened from `B13.RemainingTerminalRadius` to the refined set. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13Refine3810Main
noncomputable section

theorem main_of_energy_refine3810_and_seven_classes
    (henergy : EnergyTerminalBatchB13Refine3810.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13Refine3810.remaining_of henergy) hclasses

theorem full_disk_bound_of_energy_refine3810_and_seven_classes
    (henergy : EnergyTerminalBatchB13Refine3810.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_energy_refine3810_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13Refine3810Main
#check @N11Formalization.EnergyTerminalBatchB13Refine3810Main.main_of_energy_refine3810_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13Refine3810Main.full_disk_bound_of_energy_refine3810_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13Refine3810Main.main_of_energy_refine3810_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13Refine3810Main.full_disk_bound_of_energy_refine3810_and_seven_classes
