import N11Formalization.EnergyTerminalBatchB13RefineSeven
import N11Formalization.EnergyTerminalBatchB13Refine2337

/-! Add source terminal 2337 to the combined B13 refinement.  The paid set
has 1997 + 7 + 1 = 2005 ids; all eight new terminal/radius proofs are
dispatched explicitly. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineEight
open Finset
noncomputable section

def newIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineSeven.newIDs ∪ EnergyRefineN2337.newIDs

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13.paidIDs ∪ newIDs

theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rw [newIDs, Finset.mem_union] at hn
  rcases hn with hn | hn
  · exact EnergyTerminalBatchB13RefineSeven.new_terminal n hn
  · rw [EnergyRefineN2337.newIDs, Finset.mem_singleton] at hn
    subst n
    exact EnergyRefineN2337.terminal

theorem new_disjoint_old : Disjoint EnergyTerminalBatchB13.paidIDs newIDs := by
  rw [newIDs, Finset.disjoint_union_right]
  exact ⟨EnergyTerminalBatchB13RefineSeven.new_disjoint_old,
    EnergyTerminalBatchB13Refine2337.new_disjoint_old⟩

theorem seven_disjoint_2337 :
    Disjoint EnergyTerminalBatchB13RefineSeven.newIDs EnergyRefineN2337.newIDs := by
  decide +kernel

theorem new_count : newIDs.card = 8 := by
  rw [newIDs, Finset.card_union_of_disjoint seven_disjoint_2337,
    EnergyTerminalBatchB13RefineSeven.new_count,
    EnergyTerminalBatchB13Refine2337.new_count]

theorem paid_count : paidIDs.card = 2005 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB13.paid_count, new_count]
  norm_num

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
  · rw [newIDs, Finset.mem_union] at hn
    rcases hn with hn | hn
    · exact EnergyTerminalBatchB13RefineSeven.paid_radius n
        (Finset.mem_union_right _ hn) y hy0 hy1 hc C Z r hf
    · rw [EnergyRefineN2337.newIDs, Finset.mem_singleton] at hn
      subst n
      exact EnergyRefineN2337.new_radius _ (by simp) y hy0 hy1 hc C Z r hf

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
  · have hlt := paid_radius n (Finset.mem_union_right _ hn)
      y hy0 hy1 hc C Z r hf
    exact hlt.le
  · exact h n ht hs (by simp [paidIDs, hp, hn]) y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13RefineEight
