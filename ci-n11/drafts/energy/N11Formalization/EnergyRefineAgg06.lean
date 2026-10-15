import N11Formalization.EnergyRefineN3865
import N11Formalization.EnergyRefineN3979
import N11Formalization.EnergyRefineN4162
import N11Formalization.EnergyRefineN4244
import N11Formalization.EnergyRefineN4313
import N11Formalization.EnergyRefineN4650
import N11Formalization.EnergyRefineN4684
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.EnergyRefineAgg06
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := EnergyRefineN3865.newIDs ∪ (EnergyRefineN3979.newIDs ∪ (EnergyRefineN4162.newIDs ∪ (EnergyRefineN4244.newIDs ∪ (EnergyRefineN4313.newIDs ∪ (EnergyRefineN4650.newIDs ∪ (EnergyRefineN4684.newIDs))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ EnergyRefineN3865.newIDs ∨ n ∈ EnergyRefineN3979.newIDs ∨ n ∈ EnergyRefineN4162.newIDs ∨ n ∈ EnergyRefineN4244.newIDs ∨ n ∈ EnergyRefineN4313.newIDs ∨ n ∈ EnergyRefineN4650.newIDs ∨ n ∈ EnergyRefineN4684.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3865.new_terminal n hn
  · exact EnergyRefineN3979.new_terminal n hn
  · exact EnergyRefineN4162.new_terminal n hn
  · exact EnergyRefineN4244.new_terminal n hn
  · exact EnergyRefineN4313.new_terminal n hn
  · exact EnergyRefineN4650.new_terminal n hn
  · exact EnergyRefineN4684.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ EnergyRefineN3865.newIDs ∨ n ∈ EnergyRefineN3979.newIDs ∨ n ∈ EnergyRefineN4162.newIDs ∨ n ∈ EnergyRefineN4244.newIDs ∨ n ∈ EnergyRefineN4313.newIDs ∨ n ∈ EnergyRefineN4650.newIDs ∨ n ∈ EnergyRefineN4684.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3865.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3979.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN4162.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN4244.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN4313.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN4650.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN4684.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.EnergyRefineAgg06
#print axioms N11Formalization.EnergyRefineAgg06.new_radius
