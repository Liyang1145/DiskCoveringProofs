import N11Formalization.EnergyTerminalBatchB13RefineThirteen
import N11Formalization.EnergyTerminalBatchB13Refine3116

/-! Combine the thirteen-certificate refinement with source terminal 3116.
The paid set has 2010 + 1 = 2011 ids, leaving 376 - 1 = 375 terminals in the
explicit B13 residual predicate. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineFourteen
open Finset
noncomputable section

def newIDs : Finset (Fin 5011) := EnergyRefineN3116.newIDs

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineThirteen.paidIDs ∪ newIDs

theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  exact EnergyRefineN3116.new_terminal n hn

theorem not_paid_eleven : (3116 : Fin 5011) ∉
    EnergyTerminalBatchB13RefineEleven.paidIDs := by
  intro h
  rw [EnergyTerminalBatchB13RefineEleven.paidIDs, Finset.mem_union] at h
  rcases h with hbase | hnew
  · exact EnergyTerminalBatchB13Refine3116.not_paid_3116 hbase
  · exact (by decide +kernel :
      (3116 : Fin 5011) ∉ EnergyTerminalBatchB13RefineEleven.newIDs) hnew

theorem not_paid_twelve : (3116 : Fin 5011) ∉
    EnergyTerminalBatchB13RefineTwelve.paidIDs := by
  intro h
  rw [EnergyTerminalBatchB13RefineTwelve.paidIDs, Finset.mem_union] at h
  rcases h with hprevious | h37
  · exact not_paid_eleven hprevious
  · exact (by decide +kernel :
      (3116 : Fin 5011) ∉ EnergyRefineN0037.newIDs) h37

theorem not_paid_thirteen : (3116 : Fin 5011) ∉
    EnergyTerminalBatchB13RefineThirteen.paidIDs := by
  intro h
  rw [EnergyTerminalBatchB13RefineThirteen.paidIDs, Finset.mem_union] at h
  rcases h with hprevious | h3112
  · exact not_paid_twelve hprevious
  · exact (by decide +kernel :
      (3116 : Fin 5011) ∉ EnergyRefineN3112.newIDs) h3112

theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB13RefineThirteen.paidIDs EnergyRefineN3116.newIDs := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have ha3116 : a = 3116 := by
    simpa [EnergyRefineN3116.newIDs] using hb
  subst a
  exact not_paid_thirteen ha

theorem new_count : newIDs.card = 1 := by
  exact EnergyTerminalBatchB13Refine3116.new_count

theorem paid_count : paidIDs.card = 2011 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB13RefineThirteen.paid_count, new_count]

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineThirteen.paid_terminal n hn
  · exact EnergyRefineN3116.new_terminal n hn

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineThirteen.paid_radius n hn
      y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3116.new_radius n hn y hy0 hy1 hc C Z r hf

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
  by_cases hn : n ∈ EnergyRefineN3116.newIDs
  · exact (EnergyRefineN3116.new_radius n hn y hy0 hy1 hc C Z r hf).le
  · by_cases he : n ∈ EnergyTerminalBatchB13RefineThirteen.paidIDs
    · exact (EnergyTerminalBatchB13RefineThirteen.paid_radius n he
        y hy0 hy1 hc C Z r hf).le
    · have hrest := h n ht hs (by
        intro hpn
        rcases Finset.mem_union.mp hpn with hpn | hpn
        · exact he hpn
        · exact hn hpn)
      exact hrest y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13RefineFourteen
#check @N11Formalization.EnergyTerminalBatchB13RefineFourteen.paid_count
#check @N11Formalization.EnergyTerminalBatchB13RefineFourteen.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13RefineFourteen.remaining_of
#print axioms N11Formalization.EnergyTerminalBatchB13RefineFourteen.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13RefineFourteen.remaining_of
