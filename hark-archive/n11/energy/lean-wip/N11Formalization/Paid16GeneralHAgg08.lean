import N11Formalization.Paid16GeneralH071
import N11Formalization.Paid16GeneralH072
import N11Formalization.Paid16GeneralH073
import N11Formalization.Paid16GeneralH074
import N11Formalization.Paid16GeneralH075
import N11Formalization.Paid16GeneralH076
import N11Formalization.Paid16GeneralH077
import N11Formalization.Paid16GeneralH078
import N11Formalization.Paid16GeneralH079
import N11Formalization.Paid16GeneralH080
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg08
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH071.newIDs ∪ (Paid16GeneralH072.newIDs ∪ (Paid16GeneralH073.newIDs ∪ (Paid16GeneralH074.newIDs ∪ (Paid16GeneralH075.newIDs ∪ (Paid16GeneralH076.newIDs ∪ (Paid16GeneralH077.newIDs ∪ (Paid16GeneralH078.newIDs ∪ (Paid16GeneralH079.newIDs ∪ (Paid16GeneralH080.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH071.newIDs ∨ n ∈ Paid16GeneralH072.newIDs ∨ n ∈ Paid16GeneralH073.newIDs ∨ n ∈ Paid16GeneralH074.newIDs ∨ n ∈ Paid16GeneralH075.newIDs ∨ n ∈ Paid16GeneralH076.newIDs ∨ n ∈ Paid16GeneralH077.newIDs ∨ n ∈ Paid16GeneralH078.newIDs ∨ n ∈ Paid16GeneralH079.newIDs ∨ n ∈ Paid16GeneralH080.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH071.new_terminal n hn
  · exact Paid16GeneralH072.new_terminal n hn
  · exact Paid16GeneralH073.new_terminal n hn
  · exact Paid16GeneralH074.new_terminal n hn
  · exact Paid16GeneralH075.new_terminal n hn
  · exact Paid16GeneralH076.new_terminal n hn
  · exact Paid16GeneralH077.new_terminal n hn
  · exact Paid16GeneralH078.new_terminal n hn
  · exact Paid16GeneralH079.new_terminal n hn
  · exact Paid16GeneralH080.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH071.newIDs ∨ n ∈ Paid16GeneralH072.newIDs ∨ n ∈ Paid16GeneralH073.newIDs ∨ n ∈ Paid16GeneralH074.newIDs ∨ n ∈ Paid16GeneralH075.newIDs ∨ n ∈ Paid16GeneralH076.newIDs ∨ n ∈ Paid16GeneralH077.newIDs ∨ n ∈ Paid16GeneralH078.newIDs ∨ n ∈ Paid16GeneralH079.newIDs ∨ n ∈ Paid16GeneralH080.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH071.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH072.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH073.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH074.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH075.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH076.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH077.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH078.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH079.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH080.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg08
#print axioms N11Formalization.Paid16GeneralHAgg08.new_radius
