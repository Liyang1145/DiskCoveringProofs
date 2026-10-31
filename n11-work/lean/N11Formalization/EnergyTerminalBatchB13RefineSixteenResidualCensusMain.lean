import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus
import N11Formalization.EnergyTerminalBatchB13Main

/-! Main-thread consumer of the exact 373-id residual census.

The hypothesis remains the full residual radius certificate for every literal
id, or equivalently the explicit counter-radius packet producer.  The
seven-class premise is kept explicit.  This module composes those premises into
the final statement; it does not assert that either premise is proved. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain
open N11Formalization
noncomputable section

theorem main_of_residual373_radius_certificates_and_seven_classes
    (henergy : ∀ n,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualCensus.residual373 →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13Main.main_of_energy_b13_and_seven_classes
    (EnergyTerminalBatchB13RefineSixteenResidualCensus.b13_remaining_of_residual373_radius_certificates
      henergy)
    hclasses

theorem full_disk_bound_of_residual373_radius_certificates_and_seven_classes
    (henergy : ∀ n,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualCensus.residual373 →
        EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual373_radius_certificates_and_seven_classes henergy
      hclasses)).bounds

theorem main_of_residual373_packet_producers_and_seven_classes
    (hproducer : ∀ n,
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualCensus.residual373 →
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
      n ∈ EnergyTerminalBatchB13RefineSixteenResidualCensus.residual373 →
        EnergyTerminalBatchB13.ResidualPacketProducer n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main
    (main_of_residual373_packet_producers_and_seven_classes hproducer
      hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain.main_of_residual373_radius_certificates_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain.full_disk_bound_of_residual373_radius_certificates_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain.main_of_residual373_packet_producers_and_seven_classes
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain.full_disk_bound_of_residual373_packet_producers_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain.main_of_residual373_radius_certificates_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusMain.full_disk_bound_of_residual373_packet_producers_and_seven_classes
