import N11Formalization.Paid16GeneralH021
import N11Formalization.Paid16GeneralH022
import N11Formalization.Paid16GeneralH023
import N11Formalization.Paid16GeneralH024
import N11Formalization.Paid16GeneralH025
import N11Formalization.Paid16GeneralH026
import N11Formalization.Paid16GeneralH027
import N11Formalization.Paid16GeneralH028
import N11Formalization.Paid16GeneralH029
import N11Formalization.Paid16GeneralH030
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg03
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH021.newIDs ∪ (Paid16GeneralH022.newIDs ∪ (Paid16GeneralH023.newIDs ∪ (Paid16GeneralH024.newIDs ∪ (Paid16GeneralH025.newIDs ∪ (Paid16GeneralH026.newIDs ∪ (Paid16GeneralH027.newIDs ∪ (Paid16GeneralH028.newIDs ∪ (Paid16GeneralH029.newIDs ∪ (Paid16GeneralH030.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH021.newIDs ∨ n ∈ Paid16GeneralH022.newIDs ∨ n ∈ Paid16GeneralH023.newIDs ∨ n ∈ Paid16GeneralH024.newIDs ∨ n ∈ Paid16GeneralH025.newIDs ∨ n ∈ Paid16GeneralH026.newIDs ∨ n ∈ Paid16GeneralH027.newIDs ∨ n ∈ Paid16GeneralH028.newIDs ∨ n ∈ Paid16GeneralH029.newIDs ∨ n ∈ Paid16GeneralH030.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH021.new_terminal n hn
  · exact Paid16GeneralH022.new_terminal n hn
  · exact Paid16GeneralH023.new_terminal n hn
  · exact Paid16GeneralH024.new_terminal n hn
  · exact Paid16GeneralH025.new_terminal n hn
  · exact Paid16GeneralH026.new_terminal n hn
  · exact Paid16GeneralH027.new_terminal n hn
  · exact Paid16GeneralH028.new_terminal n hn
  · exact Paid16GeneralH029.new_terminal n hn
  · exact Paid16GeneralH030.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH021.newIDs ∨ n ∈ Paid16GeneralH022.newIDs ∨ n ∈ Paid16GeneralH023.newIDs ∨ n ∈ Paid16GeneralH024.newIDs ∨ n ∈ Paid16GeneralH025.newIDs ∨ n ∈ Paid16GeneralH026.newIDs ∨ n ∈ Paid16GeneralH027.newIDs ∨ n ∈ Paid16GeneralH028.newIDs ∨ n ∈ Paid16GeneralH029.newIDs ∨ n ∈ Paid16GeneralH030.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH021.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH022.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH023.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH024.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH025.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH026.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH027.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH028.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH029.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH030.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg03
#print axioms N11Formalization.Paid16GeneralHAgg03.new_radius
