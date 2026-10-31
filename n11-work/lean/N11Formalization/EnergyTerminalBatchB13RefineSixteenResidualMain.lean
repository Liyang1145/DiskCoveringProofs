import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
import N11Formalization.EnergyTerminalBatchB13Main

/-! Direct main-thread consumer of the repaired B13 residual interface.

This avoids depending on a literal residual census: the energy premise ranges
over `RefineSixteenResidual.residualIDs` itself.  It is an implication, not a
proof of any residual radius certificate. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualMain
open N11Formalization
noncomputable section

theorem main_of_residual_radius_certificates_and_seven_classes
    (henergy : ∀ n : Fin 5011,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13RefineSixteenResidual.b13_remaining_of_residual_radius_certificates
      henergy)
    hclasses

theorem full_disk_bound_of_residual_radius_certificates_and_seven_classes
    (henergy : ∀ n : Fin 5011,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual_radius_certificates_and_seven_classes henergy hclasses)).bounds

theorem main_of_residual_packet_producers_and_seven_classes
    (hproducer : ∀ n : Fin 5011,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs →
        EnergyTerminalBatchB13.ResidualPacketProducer n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  main_of_residual_radius_certificates_and_seven_classes
    (fun n hn => EnergyTerminalBatchB13.residual_radius_certificate_of_packet_producer
      (hproducer n hn)) hclasses

theorem full_disk_bound_of_residual_packet_producers_and_seven_classes
    (hproducer : ∀ n : Fin 5011,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs →
        EnergyTerminalBatchB13.ResidualPacketProducer n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual_packet_producers_and_seven_classes hproducer hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualMain
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualMain.main_of_residual_radius_certificates_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualMain.full_disk_bound_of_residual_packet_producers_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualMain.main_of_residual_radius_certificates_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualMain.full_disk_bound_of_residual_packet_producers_and_seven_classes
