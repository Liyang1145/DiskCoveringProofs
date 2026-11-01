import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus

/-! Structural, lane-B-owned replacement for the conflicted 373-id census.
The count is obtained from a lane-B-owned 373-id literal census reconstructed
from the terminal/packet sources; the sixteen certified ids are removed.  This proves cardinality only; it pays no
residual radius and keeps the analytic obligations explicit. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural
noncomputable section

abbrev residual373 : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residual373

theorem repair_paidIDs_eq_refineSixteen_paidIDs :
    EnergyTerminalBatchB13RefineSixteenRepair.paidIDs =
      EnergyTerminalBatchB13RefineSixteen.paidIDs := rfl

theorem residualIDs_eq_residual373 :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs = residual373 :=
  EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residualIDs_eq_residual373

theorem residual373_card : residual373.card = 373 :=
  EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus.residual373_card

theorem residualIDs_card :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs.card = 373 := by
  rw [residualIDs_eq_residual373, residual373_card]

theorem remaining_of_residual373_radius_certificates
    (h : ∀ n, n ∈ residual373 →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13RefineSixteenRepair.RemainingTerminalRadius :=
  EnergyTerminalBatchB13RefineSixteenResidual.remaining_of_residual_radius_certificates
    (fun n hn => h n ((residualIDs_eq_residual373).mp hn))

theorem b13_remaining_of_residual373_radius_certificates
    (h : ∀ n, n ∈ residual373 →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  EnergyTerminalBatchB13RefineSixteenResidual.b13_remaining_of_residual_radius_certificates
    (fun n hn => h n ((residualIDs_eq_residual373).mp hn))

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural.residualIDs_card
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural.b13_remaining_of_residual373_radius_certificates
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural.residualIDs_card
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural.b13_remaining_of_residual373_radius_certificates
