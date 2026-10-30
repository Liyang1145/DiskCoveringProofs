import N11Formalization.EnergyTerminalBatchB13RefineEleven
import N11Formalization.EnergyTerminalBatchB13Refine0037

/-! Combine the eleven-certificate refinement with source terminal 37.  The
paid set has 1997 + 11 + 1 = 2009 ids. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineTwelve
open Finset
noncomputable section

def newIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineEleven.newIDs ∪ EnergyRefineN0037.newIDs

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineEleven.paidIDs ∪ EnergyRefineN0037.newIDs

theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rw [newIDs, Finset.mem_union] at hn
  rcases hn with hn | hn
  · exact EnergyTerminalBatchB13RefineEleven.new_terminal n hn
  · exact EnergyRefineN0037.new_terminal n hn

theorem new_disjoint_eleven :
    Disjoint EnergyTerminalBatchB13RefineEleven.paidIDs EnergyRefineN0037.newIDs := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have ha37 : a = 37 := by simpa [EnergyRefineN0037.newIDs] using hb
  subst a
  rw [EnergyTerminalBatchB13RefineEleven.paidIDs, Finset.mem_union] at ha
  rcases ha with hbase | hnew
  · exact EnergyTerminalBatchB13Refine0037.not_paid_0037 hbase
  · have hnot : (37 : Fin 5011) ∉ EnergyTerminalBatchB13RefineEleven.newIDs := by
      decide +kernel
    exact hnot hnew

theorem new_count : EnergyRefineN0037.newIDs.card = 1 := by
  simp [EnergyRefineN0037.newIDs]

theorem paid_count : paidIDs.card = 2009 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_eleven,
    EnergyTerminalBatchB13RefineEleven.paid_count, new_count]

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineEleven.paid_terminal n hn
  · exact EnergyRefineN0037.new_terminal n hn

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineEleven.paid_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN0037.new_radius n hn y hy0 hy1 hc C Z r hf

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
  by_cases hn : n ∈ EnergyRefineN0037.newIDs
  · exact (EnergyRefineN0037.new_radius n hn y hy0 hy1 hc C Z r hf).le
  · by_cases he : n ∈ EnergyTerminalBatchB13RefineEleven.paidIDs
    · exact (EnergyTerminalBatchB13RefineEleven.paid_radius n he
        y hy0 hy1 hc C Z r hf).le
    · have hrest := h n ht hs (by simp [paidIDs, hn, he])
      exact hrest y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13RefineTwelve
#check @N11Formalization.EnergyTerminalBatchB13RefineTwelve.paid_count
#check @N11Formalization.EnergyTerminalBatchB13RefineTwelve.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13RefineTwelve.remaining_of
#print axioms N11Formalization.EnergyTerminalBatchB13RefineTwelve.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13RefineTwelve.remaining_of
