import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
import N11Formalization.EnergyTerminalBatchB13RefineSixteenTerminalCensus

/-! Compositional cardinality bridge for the 373-id refined residual.

`residualIDs` is definitionally a filter over all 5011 source indices.  This
module rewrites it as `terminalIDs \ (sharpIDs ∪ paidIDs)`, separating the
remaining terminal census from the already counted sharp and paid sets.  The
two census/disjointness premises are explicit; no residual radius is paid. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
open Finset
noncomputable section

/-- The sixteen ids added by the repair, kept literal so this bridge does not
import the old 389-element residual census. -/
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

theorem removed_not_sharp :
    Disjoint Patch120SharpDispatch.sharpIDs removedIDs := by
  rw [Finset.disjoint_left]
  intro n hn hs
  simp only [removedIDs, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact (by decide +kernel : _ ∉ Patch120SharpDispatch.sharpIDs) hn

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

theorem repaired_paid_not_sharp :
    Disjoint Patch120SharpDispatch.sharpIDs
      EnergyTerminalBatchB13RefineSixteenRepair.paidIDs := by
  rw [paidIDs_eq_base_union_removed, Finset.disjoint_union_right]
  exact ⟨EnergyTerminalBatchB13.paid_not_sharp.symm, removed_not_sharp⟩

theorem terminalIDs_eq_sharp_union_paid_union_residual :
    terminalIDs =
      (Patch120SharpDispatch.sharpIDs ∪
        EnergyTerminalBatchB13RefineSixteenRepair.paidIDs) ∪ residualIDs := by
  ext n
  constructor
  · intro hn
    rw [terminalIDs, Finset.mem_filter] at hn
    by_cases hs : n ∈ Patch120SharpDispatch.sharpIDs
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hs)
    · by_cases hp : n ∈ EnergyTerminalBatchB13RefineSixteenRepair.paidIDs
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hp)
      · exact Finset.mem_union_right _ ((mem_residualIDs_iff n).mpr ⟨hn.2, hs, hp⟩)
  · intro hn
    rcases Finset.mem_union.mp hn with hsp | hr
    · rcases Finset.mem_union.mp hsp with hs | hp
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ n, Patch120SharpDispatch.sharp_terminal n hs⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ n,
            EnergyTerminalBatchB13RefineSixteenRepair.paid_terminal n hp⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ n, ((mem_residualIDs_iff n).mp hr).1⟩

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

theorem residualIDs_card : residualIDs.card = 373 :=
  residualIDs_card_of_terminal_census terminalIDs_card repaired_paid_not_sharp

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.residualIDs_eq_sdiff
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.residualIDs_card_of_terminal_census
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.terminalIDs_card
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual.residualIDs_card
