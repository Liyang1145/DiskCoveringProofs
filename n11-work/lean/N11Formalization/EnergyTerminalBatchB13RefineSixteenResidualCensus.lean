import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
import N11Formalization.EnergyTerminalResidualCensusRefineSixteen

/-! Exact conditional census after the sixteen-refinement repair.
The maintained structural census is the 389-id B13 census minus the
literal sixteen-id refinement set.  Aliasing it avoids re-evaluating
the 2,013-element paid set at every source index; an earlier
51-block literal encoding exhausted kernel memory in CI.
This module proves cardinality only, not radius payment. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus
noncomputable section

abbrev residual373 : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs

theorem repair_paidIDs_eq_refineSixteen_paidIDs :
    EnergyTerminalBatchB13RefineSixteenRepair.paidIDs =
      EnergyTerminalBatchB13RefineSixteen.paidIDs := rfl

theorem residualIDs_eq_residual373 :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs = residual373 := by
  ext n
  rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff,
    EnergyTerminalResidualCensusRefineSixteen.mem_refinedResidualIDs_iff,
    repair_paidIDs_eq_refineSixteen_paidIDs]
  rfl

theorem residual373_card : residual373.card = 373 :=
  EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs_card

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
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.residualIDs_card
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.b13_remaining_of_residual373_radius_certificates
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.residualIDs_card
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.b13_remaining_of_residual373_radius_certificates
