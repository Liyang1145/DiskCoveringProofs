import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain
import N11Formalization.EnergyTerminalResidualCensusRefine346

/-! Full-disk consumer for the 346-id residual obtained by removing the 27
already-green archive refinements from lane B's 373-id interface.

This module supplies no residual radius certificate.  It only exposes the
existing exact residual interface and its conditional main-thread consumer. -/
set_option autoImplicit false
namespace N11Formalization.LaneBResidual346Bridge
open N11Formalization
noncomputable section

theorem b13_remaining_of_residual346_radius_certificates
    (h : ∀ n,
      n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  EnergyTerminalResidualCensusRefine346.b13_remaining_of_residual346
    (EnergyTerminalResidualCensusRefine346.remaining_of_radius_certificates h)

theorem main_of_residual346_radius_certificates_and_seven_classes
    (h : ∀ n,
      n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (b13_remaining_of_residual346_radius_certificates h) hclasses

theorem full_disk_bound_of_residual346_radius_certificates_and_seven_classes
    (h : ∀ n,
      n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual346_radius_certificates_and_seven_classes h hclasses)).bounds

theorem main_of_residual346_packet_producers_and_seven_classes
    (h : ∀ n,
      n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
        EnergyTerminalBatchB13.ResidualPacketProducer n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  main_of_residual346_radius_certificates_and_seven_classes
    (fun n hn =>
      EnergyTerminalBatchB13.residual_radius_certificate_of_packet_producer
        (h n hn)) hclasses

theorem full_disk_bound_of_residual346_packet_producers_and_seven_classes
    (h : ∀ n,
      n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
        EnergyTerminalBatchB13.ResidualPacketProducer n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual346_packet_producers_and_seven_classes h hclasses)).bounds

end
end N11Formalization.LaneBResidual346Bridge
#check @N11Formalization.LaneBResidual346Bridge.main_of_residual346_radius_certificates_and_seven_classes
#check @N11Formalization.LaneBResidual346Bridge.full_disk_bound_of_residual346_packet_producers_and_seven_classes
#print axioms N11Formalization.LaneBResidual346Bridge.main_of_residual346_radius_certificates_and_seven_classes
#print axioms N11Formalization.LaneBResidual346Bridge.full_disk_bound_of_residual346_packet_producers_and_seven_classes
