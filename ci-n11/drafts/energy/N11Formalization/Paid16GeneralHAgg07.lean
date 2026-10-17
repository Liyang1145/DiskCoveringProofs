import N11Formalization.Paid16GeneralH061
import N11Formalization.Paid16GeneralH062
import N11Formalization.Paid16GeneralH063
import N11Formalization.Paid16GeneralH064
import N11Formalization.Paid16GeneralH065
import N11Formalization.Paid16GeneralH066
import N11Formalization.Paid16GeneralH067
import N11Formalization.Paid16GeneralH068
import N11Formalization.Paid16GeneralH069
import N11Formalization.Paid16GeneralH070
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg07
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH061.newIDs ∪ (Paid16GeneralH062.newIDs ∪ (Paid16GeneralH063.newIDs ∪ (Paid16GeneralH064.newIDs ∪ (Paid16GeneralH065.newIDs ∪ (Paid16GeneralH066.newIDs ∪ (Paid16GeneralH067.newIDs ∪ (Paid16GeneralH068.newIDs ∪ (Paid16GeneralH069.newIDs ∪ (Paid16GeneralH070.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH061.newIDs ∨ n ∈ Paid16GeneralH062.newIDs ∨ n ∈ Paid16GeneralH063.newIDs ∨ n ∈ Paid16GeneralH064.newIDs ∨ n ∈ Paid16GeneralH065.newIDs ∨ n ∈ Paid16GeneralH066.newIDs ∨ n ∈ Paid16GeneralH067.newIDs ∨ n ∈ Paid16GeneralH068.newIDs ∨ n ∈ Paid16GeneralH069.newIDs ∨ n ∈ Paid16GeneralH070.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH061.new_terminal n hn
  · exact Paid16GeneralH062.new_terminal n hn
  · exact Paid16GeneralH063.new_terminal n hn
  · exact Paid16GeneralH064.new_terminal n hn
  · exact Paid16GeneralH065.new_terminal n hn
  · exact Paid16GeneralH066.new_terminal n hn
  · exact Paid16GeneralH067.new_terminal n hn
  · exact Paid16GeneralH068.new_terminal n hn
  · exact Paid16GeneralH069.new_terminal n hn
  · exact Paid16GeneralH070.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH061.newIDs ∨ n ∈ Paid16GeneralH062.newIDs ∨ n ∈ Paid16GeneralH063.newIDs ∨ n ∈ Paid16GeneralH064.newIDs ∨ n ∈ Paid16GeneralH065.newIDs ∨ n ∈ Paid16GeneralH066.newIDs ∨ n ∈ Paid16GeneralH067.newIDs ∨ n ∈ Paid16GeneralH068.newIDs ∨ n ∈ Paid16GeneralH069.newIDs ∨ n ∈ Paid16GeneralH070.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH061.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH062.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH063.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH064.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH065.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH066.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH067.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH068.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH069.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH070.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg07
#print axioms N11Formalization.Paid16GeneralHAgg07.new_radius
