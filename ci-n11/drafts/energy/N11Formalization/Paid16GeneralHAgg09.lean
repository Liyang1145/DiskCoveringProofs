import N11Formalization.Paid16GeneralH081
import N11Formalization.Paid16GeneralH082
import N11Formalization.Paid16GeneralH083
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg09
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH081.newIDs ∪ (Paid16GeneralH082.newIDs ∪ (Paid16GeneralH083.newIDs))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH081.newIDs ∨ n ∈ Paid16GeneralH082.newIDs ∨ n ∈ Paid16GeneralH083.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn
  · exact Paid16GeneralH081.new_terminal n hn
  · exact Paid16GeneralH082.new_terminal n hn
  · exact Paid16GeneralH083.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH081.newIDs ∨ n ∈ Paid16GeneralH082.newIDs ∨ n ∈ Paid16GeneralH083.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn
  · exact Paid16GeneralH081.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH082.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH083.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg09
#print axioms N11Formalization.Paid16GeneralHAgg09.new_radius
