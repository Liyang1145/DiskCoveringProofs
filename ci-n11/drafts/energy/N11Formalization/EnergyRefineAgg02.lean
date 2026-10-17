import N11Formalization.EnergyRefineN3112
import N11Formalization.EnergyRefineN3116
import N11Formalization.EnergyRefineN3149
import N11Formalization.EnergyRefineN3431
import N11Formalization.EnergyRefineN3432
import N11Formalization.EnergyRefineN3440
import N11Formalization.EnergyRefineN3490
import N11Formalization.EnergyRefineN3496
import N11Formalization.EnergyRefineN3517
import N11Formalization.EnergyRefineN3520
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.EnergyRefineAgg02
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := EnergyRefineN3112.newIDs ∪ (EnergyRefineN3116.newIDs ∪ (EnergyRefineN3149.newIDs ∪ (EnergyRefineN3431.newIDs ∪ (EnergyRefineN3432.newIDs ∪ (EnergyRefineN3440.newIDs ∪ (EnergyRefineN3490.newIDs ∪ (EnergyRefineN3496.newIDs ∪ (EnergyRefineN3517.newIDs ∪ (EnergyRefineN3520.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ EnergyRefineN3112.newIDs ∨ n ∈ EnergyRefineN3116.newIDs ∨ n ∈ EnergyRefineN3149.newIDs ∨ n ∈ EnergyRefineN3431.newIDs ∨ n ∈ EnergyRefineN3432.newIDs ∨ n ∈ EnergyRefineN3440.newIDs ∨ n ∈ EnergyRefineN3490.newIDs ∨ n ∈ EnergyRefineN3496.newIDs ∨ n ∈ EnergyRefineN3517.newIDs ∨ n ∈ EnergyRefineN3520.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3112.new_terminal n hn
  · exact EnergyRefineN3116.new_terminal n hn
  · exact EnergyRefineN3149.new_terminal n hn
  · exact EnergyRefineN3431.new_terminal n hn
  · exact EnergyRefineN3432.new_terminal n hn
  · exact EnergyRefineN3440.new_terminal n hn
  · exact EnergyRefineN3490.new_terminal n hn
  · exact EnergyRefineN3496.new_terminal n hn
  · exact EnergyRefineN3517.new_terminal n hn
  · exact EnergyRefineN3520.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ EnergyRefineN3112.newIDs ∨ n ∈ EnergyRefineN3116.newIDs ∨ n ∈ EnergyRefineN3149.newIDs ∨ n ∈ EnergyRefineN3431.newIDs ∨ n ∈ EnergyRefineN3432.newIDs ∨ n ∈ EnergyRefineN3440.newIDs ∨ n ∈ EnergyRefineN3490.newIDs ∨ n ∈ EnergyRefineN3496.newIDs ∨ n ∈ EnergyRefineN3517.newIDs ∨ n ∈ EnergyRefineN3520.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3112.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3116.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3149.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3431.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3432.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3440.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3490.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3496.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3517.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3520.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.EnergyRefineAgg02
#print axioms N11Formalization.EnergyRefineAgg02.new_radius
