import N11Formalization.Paid16GeneralH031
import N11Formalization.Paid16GeneralH032
import N11Formalization.Paid16GeneralH033
import N11Formalization.Paid16GeneralH034
import N11Formalization.Paid16GeneralH035
import N11Formalization.Paid16GeneralH036
import N11Formalization.Paid16GeneralH037
import N11Formalization.Paid16GeneralH038
import N11Formalization.Paid16GeneralH039
import N11Formalization.Paid16GeneralH040
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg04
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH031.newIDs ∪ (Paid16GeneralH032.newIDs ∪ (Paid16GeneralH033.newIDs ∪ (Paid16GeneralH034.newIDs ∪ (Paid16GeneralH035.newIDs ∪ (Paid16GeneralH036.newIDs ∪ (Paid16GeneralH037.newIDs ∪ (Paid16GeneralH038.newIDs ∪ (Paid16GeneralH039.newIDs ∪ (Paid16GeneralH040.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH031.newIDs ∨ n ∈ Paid16GeneralH032.newIDs ∨ n ∈ Paid16GeneralH033.newIDs ∨ n ∈ Paid16GeneralH034.newIDs ∨ n ∈ Paid16GeneralH035.newIDs ∨ n ∈ Paid16GeneralH036.newIDs ∨ n ∈ Paid16GeneralH037.newIDs ∨ n ∈ Paid16GeneralH038.newIDs ∨ n ∈ Paid16GeneralH039.newIDs ∨ n ∈ Paid16GeneralH040.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH031.new_terminal n hn
  · exact Paid16GeneralH032.new_terminal n hn
  · exact Paid16GeneralH033.new_terminal n hn
  · exact Paid16GeneralH034.new_terminal n hn
  · exact Paid16GeneralH035.new_terminal n hn
  · exact Paid16GeneralH036.new_terminal n hn
  · exact Paid16GeneralH037.new_terminal n hn
  · exact Paid16GeneralH038.new_terminal n hn
  · exact Paid16GeneralH039.new_terminal n hn
  · exact Paid16GeneralH040.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH031.newIDs ∨ n ∈ Paid16GeneralH032.newIDs ∨ n ∈ Paid16GeneralH033.newIDs ∨ n ∈ Paid16GeneralH034.newIDs ∨ n ∈ Paid16GeneralH035.newIDs ∨ n ∈ Paid16GeneralH036.newIDs ∨ n ∈ Paid16GeneralH037.newIDs ∨ n ∈ Paid16GeneralH038.newIDs ∨ n ∈ Paid16GeneralH039.newIDs ∨ n ∈ Paid16GeneralH040.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH031.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH032.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH033.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH034.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH035.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH036.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH037.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH038.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH039.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH040.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg04
#print axioms N11Formalization.Paid16GeneralHAgg04.new_radius
