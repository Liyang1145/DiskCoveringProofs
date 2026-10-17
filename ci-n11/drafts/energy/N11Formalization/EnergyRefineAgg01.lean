import N11Formalization.EnergyRefineN0003
import N11Formalization.EnergyRefineN0023
import N11Formalization.EnergyRefineN0037
import N11Formalization.EnergyRefineN0038
import N11Formalization.EnergyRefineN0039
import N11Formalization.EnergyRefineN0040
import N11Formalization.EnergyRefineN2337
import N11Formalization.EnergyRefineN2341
import N11Formalization.EnergyRefineN2965
import N11Formalization.EnergyRefineN3040
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.EnergyRefineAgg01
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := EnergyRefineN0003.newIDs ∪ (EnergyRefineN0023.newIDs ∪ (EnergyRefineN0037.newIDs ∪ (EnergyRefineN0038.newIDs ∪ (EnergyRefineN0039.newIDs ∪ (EnergyRefineN0040.newIDs ∪ (EnergyRefineN2337.newIDs ∪ (EnergyRefineN2341.newIDs ∪ (EnergyRefineN2965.newIDs ∪ (EnergyRefineN3040.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ EnergyRefineN0003.newIDs ∨ n ∈ EnergyRefineN0023.newIDs ∨ n ∈ EnergyRefineN0037.newIDs ∨ n ∈ EnergyRefineN0038.newIDs ∨ n ∈ EnergyRefineN0039.newIDs ∨ n ∈ EnergyRefineN0040.newIDs ∨ n ∈ EnergyRefineN2337.newIDs ∨ n ∈ EnergyRefineN2341.newIDs ∨ n ∈ EnergyRefineN2965.newIDs ∨ n ∈ EnergyRefineN3040.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN0003.new_terminal n hn
  · exact EnergyRefineN0023.new_terminal n hn
  · exact EnergyRefineN0037.new_terminal n hn
  · exact EnergyRefineN0038.new_terminal n hn
  · exact EnergyRefineN0039.new_terminal n hn
  · exact EnergyRefineN0040.new_terminal n hn
  · exact EnergyRefineN2337.new_terminal n hn
  · exact EnergyRefineN2341.new_terminal n hn
  · exact EnergyRefineN2965.new_terminal n hn
  · exact EnergyRefineN3040.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ EnergyRefineN0003.newIDs ∨ n ∈ EnergyRefineN0023.newIDs ∨ n ∈ EnergyRefineN0037.newIDs ∨ n ∈ EnergyRefineN0038.newIDs ∨ n ∈ EnergyRefineN0039.newIDs ∨ n ∈ EnergyRefineN0040.newIDs ∨ n ∈ EnergyRefineN2337.newIDs ∨ n ∈ EnergyRefineN2341.newIDs ∨ n ∈ EnergyRefineN2965.newIDs ∨ n ∈ EnergyRefineN3040.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN0003.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN0023.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN0037.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN0038.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN0039.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN0040.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN2337.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN2341.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN2965.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3040.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.EnergyRefineAgg01
#print axioms N11Formalization.EnergyRefineAgg01.new_radius
