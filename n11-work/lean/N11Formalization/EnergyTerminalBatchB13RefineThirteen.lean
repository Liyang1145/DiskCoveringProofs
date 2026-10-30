import N11Formalization.EnergyTerminalBatchB13RefineTwelve
import N11Formalization.EnergyTerminalBatchB13Refine3112

/-! Combine the twelve-certificate refinement with source terminal 3112.
The paid set has 1997 + 12 + 1 = 2010 ids, leaving 389 - 13 = 376 terminals in the
explicit B13 residual predicate. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineThirteen
open Finset
noncomputable section

def newIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineTwelve.newIDs ∪ EnergyRefineN3112.newIDs

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineTwelve.paidIDs ∪ EnergyRefineN3112.newIDs

theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rw [newIDs, Finset.mem_union] at hn
  rcases hn with hn | hn
  · exact EnergyTerminalBatchB13RefineTwelve.new_terminal n hn
  · exact EnergyRefineN3112.new_terminal n hn

theorem not_paid_eleven : (3112 : Fin 5011) ∉
    EnergyTerminalBatchB13RefineEleven.paidIDs := by
  intro h
  rw [EnergyTerminalBatchB13RefineEleven.paidIDs, Finset.mem_union] at h
  rcases h with hbase | hnew
  · exact EnergyTerminalBatchB13Refine3112.not_paid_3112 hbase
  · exact (by decide +kernel :
      (3112 : Fin 5011) ∉ EnergyTerminalBatchB13RefineEleven.newIDs) hnew

theorem not_paid_twelve : (3112 : Fin 5011) ∉
    EnergyTerminalBatchB13RefineTwelve.paidIDs := by
  intro h
  rw [EnergyTerminalBatchB13RefineTwelve.paidIDs, Finset.mem_union] at h
  rcases h with hnew | h37
  · exact not_paid_eleven hnew
  · exact (by decide +kernel :
      (3112 : Fin 5011) ∉ EnergyRefineN0037.newIDs) h37

theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB13RefineTwelve.paidIDs EnergyRefineN3112.newIDs := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have ha3112 : a = 3112 := by
    simpa [EnergyRefineN3112.newIDs] using hb
  subst a
  exact not_paid_twelve ha

theorem twelve_disjoint_3112 :
    Disjoint EnergyTerminalBatchB13RefineTwelve.newIDs EnergyRefineN3112.newIDs := by
  decide +kernel

theorem twelve_new_count :
    EnergyTerminalBatchB13RefineTwelve.newIDs.card = 12 := by
  have hdisj : Disjoint EnergyTerminalBatchB13RefineEleven.newIDs
      EnergyRefineN0037.newIDs := by
    decide +kernel
  rw [EnergyTerminalBatchB13RefineTwelve.newIDs,
    Finset.card_union_of_disjoint hdisj,
    EnergyTerminalBatchB13RefineEleven.new_count,
    EnergyTerminalBatchB13RefineTwelve.new_count]
  norm_num

theorem new_count : newIDs.card = 13 := by
  rw [newIDs, Finset.card_union_of_disjoint twelve_disjoint_3112,
    twelve_new_count, EnergyTerminalBatchB13Refine3112.new_count]

theorem paid_count : paidIDs.card = 2010 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB13RefineTwelve.paid_count,
    EnergyTerminalBatchB13Refine3112.new_count]

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineTwelve.paid_terminal n hn
  · exact EnergyRefineN3112.new_terminal n hn

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineTwelve.paid_radius n hn
      y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3112.new_radius n hn y hy0 hy1 hc C Z r hf

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
  by_cases hn : n ∈ EnergyRefineN3112.newIDs
  · exact (EnergyRefineN3112.new_radius n hn y hy0 hy1 hc C Z r hf).le
  · by_cases he : n ∈ EnergyTerminalBatchB13RefineTwelve.paidIDs
    · exact (EnergyTerminalBatchB13RefineTwelve.paid_radius n he
        y hy0 hy1 hc C Z r hf).le
    · have hrest := h n ht hs (by
        intro hpn
        rcases Finset.mem_union.mp hpn with hpn | hpn
        · exact he hpn
        · exact hn hpn)
      exact hrest y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13RefineThirteen
#check @N11Formalization.EnergyTerminalBatchB13RefineThirteen.paid_count
#check @N11Formalization.EnergyTerminalBatchB13RefineThirteen.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13RefineThirteen.remaining_of
#print axioms N11Formalization.EnergyTerminalBatchB13RefineThirteen.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13RefineThirteen.remaining_of
