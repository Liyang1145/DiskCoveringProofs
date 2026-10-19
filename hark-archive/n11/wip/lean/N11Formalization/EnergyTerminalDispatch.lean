import N11Formalization.Terminal984Oracle

/-! Common exactchart dispatch: ALL120 sharp plus four genuine energy
terminals. Remaining terminal lower bounds are EXPLICIT, not placeholders
hidden inside a final all-chart/global-cover theorem. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalDispatch
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) := EnergyCommonChart.paidEnergyIDs ∪ {984}
theorem paid_count : paidIDs.card=4 := by decide +kernel
theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by
  decide +kernel
theorem paid_terminal (n : Fin 5011) (hn : n∈paidIDs) :
    (DBMSourceTree.data n).terminal=true := by
  have h : n=284 ∨ n=562 ∨ n=4348 ∨ n=984 := by
    simpa only [paidIDs,EnergyCommonChart.paidEnergyIDs,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,or_assoc] using hn
  rcases h with rfl | rfl | rfl | rfl
  · exact Leaf284TreeBridge.leaf284_is_terminal
  · exact Terminal562Oracle.actual_node_is_terminal
  · exact Leaf4348TreeBridge.leaf4348_is_terminal
  · exact Terminal984Oracle.terminal984

theorem paid_radius (n : Fin 5011) (hn : n∈paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius<r := by
  have h : n∈EnergyCommonChart.paidEnergyIDs ∨ n=984 := by
    simpa only [paidIDs,Finset.mem_union,Finset.mem_singleton] using hn
  rcases h with h | rfl
  · exact EnergyCommonChart.paid_energy_radius n h y hy0 hy1 hc C Z r hf
  · exact Terminal984Oracle.common_chart_radius y hy0 hc C Z r hf

/-- All still-required non-sharp/non-paid terminal semantics on the CLOSED
simplex. Domain quantifiers match the actual tree cover; not a proven bound. -/
def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011,(DBMSourceTree.data n).terminal=true →
    n∉Patch120SharpDispatch.sharpIDs → n∉paidIDs →
    ∀ (y : Fin 9 → ℝ),(∀ q,0≤y q) → (∑ q,y q=1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius≤r

/-- Shared truechart whole-tree consumer, explicitly conditional on every
remaining terminal. This is NOT the unrestricted arbitrary Covers theorem. -/
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
end N11Formalization.EnergyTerminalDispatch
#check @N11Formalization.EnergyTerminalDispatch.paid_count
#check @N11Formalization.EnergyTerminalDispatch.paid_radius
#check @N11Formalization.EnergyTerminalDispatch.chart_radius_of_remaining
#print axioms N11Formalization.EnergyTerminalDispatch.paid_radius
