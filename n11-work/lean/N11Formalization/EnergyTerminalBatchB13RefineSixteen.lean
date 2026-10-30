import N11Formalization.EnergyTerminalBatchB13RefineFourteen
import N11Formalization.EnergyTerminalBatchB13Refine3431
import N11Formalization.EnergyTerminalBatchB13Refine3573

/-! Add the independently certified terminals 3431 and 3573 to the
fourteen-certificate refinement.  The paid set grows from 2011 to 2013,
leaving 389 - 16 = 373 terminal radii in the explicit B13 residual predicate. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteen
open Finset
noncomputable section

def newIDs : Finset (Fin 5011) :=
  EnergyRefineN3431.newIDs ∪ EnergyRefineN3573.newIDs

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13RefineFourteen.paidIDs ∪ newIDs

private theorem not_paid_fourteen_of {x : Fin 5011}
    (hbase : x ∉ EnergyTerminalBatchB13.paidIDs)
    (h11 : x ∉ EnergyTerminalBatchB13RefineEleven.newIDs)
    (h37 : x ∉ EnergyRefineN0037.newIDs)
    (h3112 : x ∉ EnergyRefineN3112.newIDs)
    (h3116 : x ∉ EnergyRefineN3116.newIDs) :
    x ∉ EnergyTerminalBatchB13RefineFourteen.paidIDs := by
  intro hx
  simp only [EnergyTerminalBatchB13RefineFourteen.paidIDs,
    EnergyTerminalBatchB13RefineThirteen.paidIDs,
    EnergyTerminalBatchB13RefineTwelve.paidIDs,
    EnergyTerminalBatchB13RefineEleven.paidIDs, Finset.mem_union] at hx
  tauto

private theorem not_paid_3431 :
    (3431 : Fin 5011) ∉ EnergyTerminalBatchB13RefineFourteen.paidIDs :=
  not_paid_fourteen_of EnergyTerminalBatchB13Refine3431.not_paid_3431
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

private theorem not_paid_3573 :
    (3573 : Fin 5011) ∉ EnergyTerminalBatchB13RefineFourteen.paidIDs :=
  not_paid_fourteen_of EnergyTerminalBatchB13Refine3573.not_paid_3573
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rw [newIDs, Finset.mem_union] at hn
  rcases hn with hn | hn
  · exact EnergyRefineN3431.new_terminal n hn
  · exact EnergyRefineN3573.new_terminal n hn

theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB13RefineFourteen.paidIDs newIDs := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [newIDs, Finset.mem_union] at hb
  rcases hb with hb | hb
  · have ha' : a = 3431 := by simpa [EnergyRefineN3431.newIDs] using hb
    subst a
    exact not_paid_3431 ha
  · have ha' : a = 3573 := by simpa [EnergyRefineN3573.newIDs] using hb
    subst a
    exact not_paid_3573 ha

theorem new_count : newIDs.card = 2 := by
  decide +kernel

theorem paid_count : paidIDs.card = 2013 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB13RefineFourteen.paid_count, new_count]

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineFourteen.paid_terminal n hn
  · exact new_terminal n hn

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13RefineFourteen.paid_radius n hn
      y hy0 hy1 hc C Z r hf
  · rw [newIDs, Finset.mem_union] at hn
    rcases hn with hn | hn
    · exact EnergyRefineN3431.new_radius n hn y hy0 hy1 hc C Z r hf
    · exact EnergyRefineN3573.new_radius n hn y hy0 hy1 hc C Z r hf

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
  · exact (paid_radius n (Finset.mem_union_right _ hn)
      y hy0 hy1 hc C Z r hf).le
  · by_cases he : n ∈ EnergyTerminalBatchB13RefineFourteen.paidIDs
    · exact (EnergyTerminalBatchB13RefineFourteen.paid_radius n he
        y hy0 hy1 hc C Z r hf).le
    · exact h n ht hs (by simp [paidIDs, hn, he]) y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteen
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteen.paid_count
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteen.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13RefineSixteen.remaining_of
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteen.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteen.remaining_of
