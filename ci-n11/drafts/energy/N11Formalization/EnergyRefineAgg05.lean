import N11Formalization.EnergyRefineN3807
import N11Formalization.EnergyRefineN3808
import N11Formalization.EnergyRefineN3810
import N11Formalization.EnergyRefineN3821
import N11Formalization.EnergyRefineN3825
import N11Formalization.EnergyRefineN3841
import N11Formalization.EnergyRefineN3851
import N11Formalization.EnergyRefineN3853
import N11Formalization.EnergyRefineN3854
import N11Formalization.EnergyRefineN3863
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.EnergyRefineAgg05
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := EnergyRefineN3807.newIDs ∪ (EnergyRefineN3808.newIDs ∪ (EnergyRefineN3810.newIDs ∪ (EnergyRefineN3821.newIDs ∪ (EnergyRefineN3825.newIDs ∪ (EnergyRefineN3841.newIDs ∪ (EnergyRefineN3851.newIDs ∪ (EnergyRefineN3853.newIDs ∪ (EnergyRefineN3854.newIDs ∪ (EnergyRefineN3863.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ EnergyRefineN3807.newIDs ∨ n ∈ EnergyRefineN3808.newIDs ∨ n ∈ EnergyRefineN3810.newIDs ∨ n ∈ EnergyRefineN3821.newIDs ∨ n ∈ EnergyRefineN3825.newIDs ∨ n ∈ EnergyRefineN3841.newIDs ∨ n ∈ EnergyRefineN3851.newIDs ∨ n ∈ EnergyRefineN3853.newIDs ∨ n ∈ EnergyRefineN3854.newIDs ∨ n ∈ EnergyRefineN3863.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3807.new_terminal n hn
  · exact EnergyRefineN3808.new_terminal n hn
  · exact EnergyRefineN3810.new_terminal n hn
  · exact EnergyRefineN3821.new_terminal n hn
  · exact EnergyRefineN3825.new_terminal n hn
  · exact EnergyRefineN3841.new_terminal n hn
  · exact EnergyRefineN3851.new_terminal n hn
  · exact EnergyRefineN3853.new_terminal n hn
  · exact EnergyRefineN3854.new_terminal n hn
  · exact EnergyRefineN3863.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ EnergyRefineN3807.newIDs ∨ n ∈ EnergyRefineN3808.newIDs ∨ n ∈ EnergyRefineN3810.newIDs ∨ n ∈ EnergyRefineN3821.newIDs ∨ n ∈ EnergyRefineN3825.newIDs ∨ n ∈ EnergyRefineN3841.newIDs ∨ n ∈ EnergyRefineN3851.newIDs ∨ n ∈ EnergyRefineN3853.newIDs ∨ n ∈ EnergyRefineN3854.newIDs ∨ n ∈ EnergyRefineN3863.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3807.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3808.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3810.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3821.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3825.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3841.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3851.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3853.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3854.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3863.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.EnergyRefineAgg05
#print axioms N11Formalization.EnergyRefineAgg05.new_radius
