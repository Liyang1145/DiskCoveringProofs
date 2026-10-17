import N11Formalization.EnergyTerminalBatchB01
import N11Formalization.TerminalDualConsumers

/-! Seven actual energy terminals on the SAME closed truechart.
RemainingTerminalRadius is explicit and UNPROVED, not a global theorem. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB02
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) := EnergyTerminalBatchB01.paidIDs ∪ {2162}
theorem paid_count : paidIDs.card=7 := by decide +kernel
theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
theorem paid_terminal (n : Fin 5011) (hn : n∈paidIDs) :
    (DBMSourceTree.data n).terminal=true := by
  have h : n∈EnergyTerminalBatchB01.paidIDs ∨ n=2162 := by
    simpa only [paidIDs,Finset.mem_union,Finset.mem_singleton] using hn
  rcases h with h | rfl
  · exact EnergyTerminalBatchB01.paid_terminal n h
  · exact TerminalDualConsumers.Own2162.terminal
theorem paid_radius (n : Fin 5011) (hn : n∈paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius < r := by
  have h : n∈EnergyTerminalBatchB01.paidIDs ∨ n=2162 := by
    simpa only [paidIDs,Finset.mem_union,Finset.mem_singleton] using hn
  rcases h with h | rfl
  · exact EnergyTerminalBatchB01.paid_radius n h y hy0 hy1 hc C Z r hf
  · exact TerminalDualConsumers.Own2162.common_chart_radius y hy0 hy1 hc C Z r hf

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
end N11Formalization.EnergyTerminalBatchB02
#check @N11Formalization.EnergyTerminalBatchB02.paid_count
#check @N11Formalization.EnergyTerminalBatchB02.paid_radius
#check @N11Formalization.EnergyTerminalBatchB02.chart_radius_of_remaining
#print axioms N11Formalization.EnergyTerminalBatchB02.paid_radius
