import N11Formalization.EnergyTerminalBatchB13
import N11Formalization.EnergyTerminalBatchB13Refine2341
import N11Formalization.EnergyTerminalBatchB13Refine3040
import N11Formalization.EnergyTerminalBatchB13Refine2965
import N11Formalization.EnergyTerminalBatchB13Refine3440
import N11Formalization.EnergyTerminalBatchB13Refine3589
import N11Formalization.EnergyTerminalBatchB13Refine3623
import N11Formalization.EnergyTerminalBatchB13Refine3633

/-! Combine the seven recovered residual singleton refinements into one B13
refinement.  The paid set has 1997 + 7 = 2004 ids and the remaining-radius
premise excludes all seven certificates at once. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSeven
open Finset
noncomputable section

def newIDs : Finset (Fin 5011) :=
  EnergyRefineN2341.newIDs ∪ EnergyRefineN3040.newIDs ∪
  EnergyRefineN2965.newIDs ∪ EnergyRefineN3440.newIDs ∪
  EnergyRefineN3589.newIDs ∪ EnergyRefineN3623.newIDs ∪
  EnergyRefineN3633.newIDs

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13.paidIDs ∪ newIDs

theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  simp only [newIDs, Finset.mem_union] at hn
  rcases hn with (((((hn | hn) | hn) | hn) | hn) | hn) | hn
  · exact EnergyRefineN2341.new_terminal n hn
  · exact EnergyRefineN3040.new_terminal n hn
  · exact EnergyRefineN2965.new_terminal n hn
  · exact EnergyRefineN3440.new_terminal n hn
  · exact EnergyRefineN3589.new_terminal n hn
  · exact EnergyRefineN3623.new_terminal n hn
  · exact EnergyRefineN3633.new_terminal n hn

theorem new_disjoint_old : Disjoint EnergyTerminalBatchB13.paidIDs newIDs := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [newIDs, Finset.mem_union] at hb
  rcases hb with (((((hb | hb) | hb) | hb) | hb) | hb) | hb
  · exact Finset.disjoint_left.mp
      EnergyTerminalBatchB13Refine2341.new_disjoint_old ha hb
  · exact Finset.disjoint_left.mp
      EnergyTerminalBatchB13Refine3040.new_disjoint_old ha hb
  · exact Finset.disjoint_left.mp
      EnergyTerminalBatchB13Refine2965.new_disjoint_old ha hb
  · exact Finset.disjoint_left.mp
      EnergyTerminalBatchB13Refine3440.new_disjoint_old ha hb
  · exact Finset.disjoint_left.mp
      EnergyTerminalBatchB13Refine3589.new_disjoint_old ha hb
  · exact Finset.disjoint_left.mp
      EnergyTerminalBatchB13Refine3623.new_disjoint_old ha hb
  · exact Finset.disjoint_left.mp
      EnergyTerminalBatchB13Refine3633.new_disjoint_old ha hb

theorem new_count : newIDs.card = 7 := by
  decide +kernel

theorem paid_count : paidIDs.card = 2004 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB13.paid_count, new_count]

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13.paid_terminal n hn
  · exact new_terminal n hn

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13.paid_radius n hn y hy0 hy1 hc C Z r hf
  · simp only [newIDs, Finset.mem_union] at hn
    rcases hn with (((((hn | hn) | hn) | hn) | hn) | hn) | hn
    · exact EnergyRefineN2341.new_radius n hn y hy0 hy1 hc C Z r hf
    · exact EnergyRefineN3040.new_radius n hn y hy0 hy1 hc C Z r hf
    · exact EnergyRefineN2965.new_radius n hn y hy0 hy1 hc C Z r hf
    · exact EnergyRefineN3440.new_radius n hn y hy0 hy1 hc C Z r hf
    · exact EnergyRefineN3589.new_radius n hn y hy0 hy1 hc C Z r hf
    · exact EnergyRefineN3623.new_radius n hn y hy0 hy1 hc C Z r hf
    · exact EnergyRefineN3633.new_radius n hn y hy0 hy1 hc C Z r hf

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, (DBMSourceTree.data n).terminal = true →
    n ∉ Patch120SharpDispatch.sharpIDs → n ∉ paidIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

theorem remaining_of (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  intro n ht hs hp y hy0 hy1 hc C Z r hf
  by_cases hn : n ∈ newIDs
  · have hlt := paid_radius n (Finset.mem_union_right _ hn) y hy0 hy1 hc C Z r hf
    exact hlt.le
  · exact h n ht hs (by simp [paidIDs, hp, hn]) y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13RefineSeven
#check @N11Formalization.EnergyTerminalBatchB13RefineSeven.paid_count
#check @N11Formalization.EnergyTerminalBatchB13RefineSeven.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13RefineSeven.remaining_of
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSeven.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSeven.remaining_of
