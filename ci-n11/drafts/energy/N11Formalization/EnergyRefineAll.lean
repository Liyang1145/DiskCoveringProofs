import N11Formalization.EnergyRefineAgg01
import N11Formalization.EnergyRefineAgg02
import N11Formalization.EnergyRefineAgg03
import N11Formalization.EnergyRefineAgg04
import N11Formalization.EnergyRefineAgg05
import N11Formalization.EnergyRefineAgg06
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.EnergyRefineAll
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := EnergyRefineAgg01.newIDs ∪ (EnergyRefineAgg02.newIDs ∪ (EnergyRefineAgg03.newIDs ∪ (EnergyRefineAgg04.newIDs ∪ (EnergyRefineAgg05.newIDs ∪ (EnergyRefineAgg06.newIDs)))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ EnergyRefineAgg01.newIDs ∨ n ∈ EnergyRefineAgg02.newIDs ∨ n ∈ EnergyRefineAgg03.newIDs ∨ n ∈ EnergyRefineAgg04.newIDs ∨ n ∈ EnergyRefineAgg05.newIDs ∨ n ∈ EnergyRefineAgg06.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn
  · exact EnergyRefineAgg01.new_terminal n hn
  · exact EnergyRefineAgg02.new_terminal n hn
  · exact EnergyRefineAgg03.new_terminal n hn
  · exact EnergyRefineAgg04.new_terminal n hn
  · exact EnergyRefineAgg05.new_terminal n hn
  · exact EnergyRefineAgg06.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ EnergyRefineAgg01.newIDs ∨ n ∈ EnergyRefineAgg02.newIDs ∨ n ∈ EnergyRefineAgg03.newIDs ∨ n ∈ EnergyRefineAgg04.newIDs ∨ n ∈ EnergyRefineAgg05.newIDs ∨ n ∈ EnergyRefineAgg06.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn
  · exact EnergyRefineAgg01.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineAgg02.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineAgg03.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineAgg04.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineAgg05.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineAgg06.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.EnergyRefineAll
#print axioms N11Formalization.EnergyRefineAll.new_radius
