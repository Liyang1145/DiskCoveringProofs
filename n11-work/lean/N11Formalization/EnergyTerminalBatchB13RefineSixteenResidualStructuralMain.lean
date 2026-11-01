import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural
import N11Formalization.EnergyTerminalBatchB13Main

/-! Main-thread consumer of the structural 373-id residual interface.  The
373 radius certificates and the seven-class exclusions remain explicit
premises; this module proves only their conditional composition. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain
open N11Formalization
noncomputable section

theorem main_of_residual373_radius_certificates_and_seven_classes
    (henergy : ∀ n,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualStructural.residual373 →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13RefineSixteenResidualStructural.b13_remaining_of_residual373_radius_certificates
      henergy)
    hclasses

theorem full_disk_bound_of_residual373_radius_certificates_and_seven_classes
    (henergy : ∀ n,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualStructural.residual373 →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual373_radius_certificates_and_seven_classes henergy
      hclasses)).bounds

theorem main_of_residual373_packet_producers_and_seven_classes
    (hproducer : ∀ n,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualStructural.residual373 →
        EnergyTerminalBatchB13.ResidualPacketProducer n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  main_of_residual373_radius_certificates_and_seven_classes
    (fun n hn =>
      EnergyTerminalBatchB13.residual_radius_certificate_of_packet_producer
        (hproducer n hn))
    hclasses

theorem full_disk_bound_of_residual373_packet_producers_and_seven_classes
    (hproducer : ∀ n,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualStructural.residual373 →
        EnergyTerminalBatchB13.ResidualPacketProducer n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual373_packet_producers_and_seven_classes hproducer
      hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain.main_of_residual373_radius_certificates_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain.full_disk_bound_of_residual373_radius_certificates_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain.main_of_residual373_packet_producers_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain.full_disk_bound_of_residual373_packet_producers_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain.main_of_residual373_radius_certificates_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain.full_disk_bound_of_residual373_packet_producers_and_seven_classes
