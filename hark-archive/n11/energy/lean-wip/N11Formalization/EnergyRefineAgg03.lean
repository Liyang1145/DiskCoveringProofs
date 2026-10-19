import N11Formalization.EnergyRefineN3522
import N11Formalization.EnergyRefineN3550
import N11Formalization.EnergyRefineN3564
import N11Formalization.EnergyRefineN3569
import N11Formalization.EnergyRefineN3573
import N11Formalization.EnergyRefineN3578
import N11Formalization.EnergyRefineN3589
import N11Formalization.EnergyRefineN3623
import N11Formalization.EnergyRefineN3633
import N11Formalization.EnergyRefineN3738
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.EnergyRefineAgg03
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := EnergyRefineN3522.newIDs ∪ (EnergyRefineN3550.newIDs ∪ (EnergyRefineN3564.newIDs ∪ (EnergyRefineN3569.newIDs ∪ (EnergyRefineN3573.newIDs ∪ (EnergyRefineN3578.newIDs ∪ (EnergyRefineN3589.newIDs ∪ (EnergyRefineN3623.newIDs ∪ (EnergyRefineN3633.newIDs ∪ (EnergyRefineN3738.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ EnergyRefineN3522.newIDs ∨ n ∈ EnergyRefineN3550.newIDs ∨ n ∈ EnergyRefineN3564.newIDs ∨ n ∈ EnergyRefineN3569.newIDs ∨ n ∈ EnergyRefineN3573.newIDs ∨ n ∈ EnergyRefineN3578.newIDs ∨ n ∈ EnergyRefineN3589.newIDs ∨ n ∈ EnergyRefineN3623.newIDs ∨ n ∈ EnergyRefineN3633.newIDs ∨ n ∈ EnergyRefineN3738.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3522.new_terminal n hn
  · exact EnergyRefineN3550.new_terminal n hn
  · exact EnergyRefineN3564.new_terminal n hn
  · exact EnergyRefineN3569.new_terminal n hn
  · exact EnergyRefineN3573.new_terminal n hn
  · exact EnergyRefineN3578.new_terminal n hn
  · exact EnergyRefineN3589.new_terminal n hn
  · exact EnergyRefineN3623.new_terminal n hn
  · exact EnergyRefineN3633.new_terminal n hn
  · exact EnergyRefineN3738.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ EnergyRefineN3522.newIDs ∨ n ∈ EnergyRefineN3550.newIDs ∨ n ∈ EnergyRefineN3564.newIDs ∨ n ∈ EnergyRefineN3569.newIDs ∨ n ∈ EnergyRefineN3573.newIDs ∨ n ∈ EnergyRefineN3578.newIDs ∨ n ∈ EnergyRefineN3589.newIDs ∨ n ∈ EnergyRefineN3623.newIDs ∨ n ∈ EnergyRefineN3633.newIDs ∨ n ∈ EnergyRefineN3738.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3522.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3550.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3564.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3569.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3573.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3578.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3589.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3623.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3633.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3738.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.EnergyRefineAgg03
#print axioms N11Formalization.EnergyRefineAgg03.new_radius
