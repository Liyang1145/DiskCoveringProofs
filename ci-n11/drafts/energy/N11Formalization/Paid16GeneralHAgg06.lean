import N11Formalization.Paid16GeneralH051
import N11Formalization.Paid16GeneralH052
import N11Formalization.Paid16GeneralH053
import N11Formalization.Paid16GeneralH054
import N11Formalization.Paid16GeneralH055
import N11Formalization.Paid16GeneralH056
import N11Formalization.Paid16GeneralH057
import N11Formalization.Paid16GeneralH058
import N11Formalization.Paid16GeneralH059
import N11Formalization.Paid16GeneralH060
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg06
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH051.newIDs ∪ (Paid16GeneralH052.newIDs ∪ (Paid16GeneralH053.newIDs ∪ (Paid16GeneralH054.newIDs ∪ (Paid16GeneralH055.newIDs ∪ (Paid16GeneralH056.newIDs ∪ (Paid16GeneralH057.newIDs ∪ (Paid16GeneralH058.newIDs ∪ (Paid16GeneralH059.newIDs ∪ (Paid16GeneralH060.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH051.newIDs ∨ n ∈ Paid16GeneralH052.newIDs ∨ n ∈ Paid16GeneralH053.newIDs ∨ n ∈ Paid16GeneralH054.newIDs ∨ n ∈ Paid16GeneralH055.newIDs ∨ n ∈ Paid16GeneralH056.newIDs ∨ n ∈ Paid16GeneralH057.newIDs ∨ n ∈ Paid16GeneralH058.newIDs ∨ n ∈ Paid16GeneralH059.newIDs ∨ n ∈ Paid16GeneralH060.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH051.new_terminal n hn
  · exact Paid16GeneralH052.new_terminal n hn
  · exact Paid16GeneralH053.new_terminal n hn
  · exact Paid16GeneralH054.new_terminal n hn
  · exact Paid16GeneralH055.new_terminal n hn
  · exact Paid16GeneralH056.new_terminal n hn
  · exact Paid16GeneralH057.new_terminal n hn
  · exact Paid16GeneralH058.new_terminal n hn
  · exact Paid16GeneralH059.new_terminal n hn
  · exact Paid16GeneralH060.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH051.newIDs ∨ n ∈ Paid16GeneralH052.newIDs ∨ n ∈ Paid16GeneralH053.newIDs ∨ n ∈ Paid16GeneralH054.newIDs ∨ n ∈ Paid16GeneralH055.newIDs ∨ n ∈ Paid16GeneralH056.newIDs ∨ n ∈ Paid16GeneralH057.newIDs ∨ n ∈ Paid16GeneralH058.newIDs ∨ n ∈ Paid16GeneralH059.newIDs ∨ n ∈ Paid16GeneralH060.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH051.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH052.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH053.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH054.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH055.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH056.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH057.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH058.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH059.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH060.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg06
#print axioms N11Formalization.Paid16GeneralHAgg06.new_radius
