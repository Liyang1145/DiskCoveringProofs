import N11Formalization.EnergyTerminalBatchB13RefineSixteenRepair
import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
import N11Formalization.EnergyTerminalResidualCensus

/-! Structural census of the repaired residual.  Rather than deciding
membership in the whole 2013-element paid set at every source index, this
module identifies the sixteen added ids explicitly and removes them from the
already assembled 389-element B13 census.  It proves cardinality only. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff
open Finset
noncomputable section

def removedIDs : Finset (Fin 5011) :=
  {37, 2337, 2341, 2965, 3040, 3112, 3116, 3431,
   3440, 3573, 3589, 3623, 3633, 3777, 3792, 3853}

theorem paidIDs_eq_base_union_removed :
    EnergyTerminalBatchB13RefineSixteenRepair.paidIDs =
      EnergyTerminalBatchB13.paidIDs ∪ removedIDs := by
  ext n
  simp only [EnergyTerminalBatchB13RefineSixteenRepair.paidIDs,
    EnergyTerminalBatchB13RefineSixteenRepair.newIDs,
    EnergyTerminalBatchB13RefineFourteen.paidIDs,
    EnergyTerminalBatchB13RefineFourteen.newIDs,
    EnergyTerminalBatchB13RefineThirteen.paidIDs,
    EnergyTerminalBatchB13RefineTwelve.paidIDs,
    EnergyTerminalBatchB13RefineEleven.paidIDs,
    EnergyTerminalBatchB13RefineEleven.newIDs,
    EnergyTerminalBatchB13RefineEight.newIDs,
    EnergyTerminalBatchB13RefineSeven.newIDs,
    EnergyRefineN3431.newIDs, EnergyRefineN3573.newIDs,
    EnergyRefineN3116.newIDs, EnergyRefineN3112.newIDs,
    EnergyRefineN0037.newIDs, EnergyRefineN3853.newIDs,
    EnergyRefineN3792.newIDs, EnergyRefineN3777.newIDs,
    EnergyRefineN2337.newIDs, EnergyRefineN2341.newIDs,
    EnergyRefineN3040.newIDs, EnergyRefineN2965.newIDs,
    EnergyRefineN3440.newIDs, EnergyRefineN3589.newIDs,
    EnergyRefineN3623.newIDs, EnergyRefineN3633.newIDs,
    removedIDs, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem residualIDs_eq_sdiff :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs =
      EnergyTerminalResidualCensus.residualIDs \ removedIDs := by
  ext n
  rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff,
    Finset.mem_sdiff, EnergyTerminalResidualCensus.residualIDs_eq,
    EnergyTerminalBatchB13.mem_residualIDs_iff,
    paidIDs_eq_base_union_removed]
  tauto

theorem removedIDs_subset :
    removedIDs ⊆ EnergyTerminalResidualCensus.residualIDs := by
  intro n hn
  simp only [removedIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [EnergyTerminalResidualCensus.residualIDs_eq,
      EnergyTerminalBatchB13.mem_residualIDs_iff]
    decide +kernel

theorem removedIDs_card : removedIDs.card = 16 := by
  decide +kernel

theorem residualIDs_card :
    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs.card = 373 := by
  rw [residualIDs_eq_sdiff, Finset.card_sdiff removedIDs_subset,
    EnergyTerminalResidualCensus.residualIDs_card, removedIDs_card]

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff.residualIDs_card
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff.residualIDs_card
