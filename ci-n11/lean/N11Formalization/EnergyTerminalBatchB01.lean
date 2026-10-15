import N11Formalization.EnergyTerminalDispatch
import N11Formalization.Terminal1112Oracle
import N11Formalization.Terminal2166Oracle

/-! Six genuine energy terminal consumers on the SAME closed true chart.
The remaining terminal semantics are explicitly unproved, not an axiom.
Own1112/2166 intervals and actualfield10 semantics, not recorded LP values. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB01
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) := EnergyTerminalDispatch.paidIDs ∪ {1112,2166}
theorem paid_count : paidIDs.card=6 := by decide +kernel
theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by
  decide +kernel
theorem paid_terminal (n : Fin 5011) (hn : n∈paidIDs) :
    (DBMSourceTree.data n).terminal=true := by
  have h : n∈EnergyTerminalDispatch.paidIDs ∨ n=1112 ∨ n=2166 := by
    simpa only [paidIDs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] using hn
  rcases h with h | rfl | rfl
  · exact EnergyTerminalDispatch.paid_terminal n h
  · exact Terminal1112Oracle.terminal
  · exact Terminal2166Oracle.terminal

theorem paid_radius (n : Fin 5011) (hn : n∈paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius<r := by
  have h : n∈EnergyTerminalDispatch.paidIDs ∨ n=1112 ∨ n=2166 := by
    simpa only [paidIDs,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] using hn
  rcases h with h | rfl | rfl
  · exact EnergyTerminalDispatch.paid_radius n h y hy0 hy1 hc C Z r hf
  · exact Terminal1112Oracle.common_chart_radius y hy0 hc C Z r hf
  · exact Terminal2166Oracle.common_chart_radius y hy0 hc C Z r hf

/-- Unpaid nonsharp/nonpaid terminals, on the entire CLOSED simplex.
No proof of this proposition is supplied or implied by the six-ID dispatch. -/
def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011,(DBMSourceTree.data n).terminal=true →
    n∉Patch120SharpDispatch.sharpIDs → n∉paidIDs →
    ∀ (y : Fin 9 → ℝ),(∀ q,0≤y q) → (∑ q,y q=1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius≤r

theorem chart_radius_of_remaining (hremaining : RemainingTerminalRadius)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius≤r := by
  obtain ⟨n,ht,hc⟩ := DBMTreeChartConsumer.chart9_terminal_cover y hy0 hy1
  by_cases hs : n∈Patch120SharpDispatch.sharpIDs
  · exact Patch120SharpDispatch.sharp_radius n hs y hc C Z r hf
  · by_cases he : n∈paidIDs
    · exact (paid_radius n he y hy0 hy1 hc C Z r hf).le
    · exact hremaining n ht hs he y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB01
#check @N11Formalization.EnergyTerminalBatchB01.paid_count
#check @N11Formalization.EnergyTerminalBatchB01.paid_terminal
#check @N11Formalization.EnergyTerminalBatchB01.paid_radius
#check @N11Formalization.EnergyTerminalBatchB01.chart_radius_of_remaining
#print axioms N11Formalization.EnergyTerminalBatchB01.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB01.chart_radius_of_remaining
