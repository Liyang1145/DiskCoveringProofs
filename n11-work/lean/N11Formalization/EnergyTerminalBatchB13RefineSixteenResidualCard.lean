import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual

/-! Compositional cardinality bridge for the 373-id refined residual.

`residualIDs` is definitionally a filter over all 5011 source indices.  This
module rewrites it as `terminalIDs \ (sharpIDs ∪ paidIDs)`, separating the
remaining terminal census from the already counted sharp and paid sets.  The
two census/disjointness premises are explicit; no residual radius is paid. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
open Finset
noncomputable section

def terminalIDs : Finset (Fin 5011) :=
  Finset.univ.filter fun n => (DBMSourceTree.data n).terminal = true

theorem residualIDs_eq_sdiff :
    residualIDs = terminalIDs \
      (Patch120SharpDispatch.sharpIDs ∪ EnergyTerminalBatchB13RefineSixteenRepair.paidIDs) := by
  ext n
  simp only [residualIDs, terminalIDs, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff, Finset.mem_union, not_or]

theorem sharp_union_paid_subset_terminal :
    Patch120SharpDispatch.sharpIDs ∪ EnergyTerminalBatchB13RefineSixteenRepair.paidIDs ⊆
      terminalIDs := by
  intro n hn
  rw [terminalIDs, Finset.mem_filter]
  refine ⟨Finset.mem_univ n, ?_⟩
  rcases Finset.mem_union.mp hn with hs | hp
  · exact Patch120SharpDispatch.sharp_terminal n hs
  · exact EnergyTerminalBatchB13RefineSixteenRepair.paid_terminal n hp

theorem residualIDs_card_of_terminal_census
    (hterminal : terminalIDs.card = 2506)
    (hdisjoint : Disjoint Patch120SharpDispatch.sharpIDs
      EnergyTerminalBatchB13RefineSixteenRepair.paidIDs) :
    residualIDs.card = 373 := by
  rw [residualIDs_eq_sdiff,
    Finset.card_sdiff_of_subset sharp_union_paid_subset_terminal,
    Finset.card_union_of_disjoint hdisjoint,
    Patch120SharpDispatch.sharp_count,
    EnergyTerminalBatchB13RefineSixteenRepair.paid_count, hterminal]
  norm_num

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.residualIDs_eq_sdiff
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.residualIDs_card_of_terminal_census
