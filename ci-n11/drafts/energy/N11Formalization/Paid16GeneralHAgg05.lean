import N11Formalization.Paid16GeneralH041
import N11Formalization.Paid16GeneralH042
import N11Formalization.Paid16GeneralH043
import N11Formalization.Paid16GeneralH044
import N11Formalization.Paid16GeneralH045
import N11Formalization.Paid16GeneralH046
import N11Formalization.Paid16GeneralH047
import N11Formalization.Paid16GeneralH048
import N11Formalization.Paid16GeneralH049
import N11Formalization.Paid16GeneralH050
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg05
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH041.newIDs ∪ (Paid16GeneralH042.newIDs ∪ (Paid16GeneralH043.newIDs ∪ (Paid16GeneralH044.newIDs ∪ (Paid16GeneralH045.newIDs ∪ (Paid16GeneralH046.newIDs ∪ (Paid16GeneralH047.newIDs ∪ (Paid16GeneralH048.newIDs ∪ (Paid16GeneralH049.newIDs ∪ (Paid16GeneralH050.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH041.newIDs ∨ n ∈ Paid16GeneralH042.newIDs ∨ n ∈ Paid16GeneralH043.newIDs ∨ n ∈ Paid16GeneralH044.newIDs ∨ n ∈ Paid16GeneralH045.newIDs ∨ n ∈ Paid16GeneralH046.newIDs ∨ n ∈ Paid16GeneralH047.newIDs ∨ n ∈ Paid16GeneralH048.newIDs ∨ n ∈ Paid16GeneralH049.newIDs ∨ n ∈ Paid16GeneralH050.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH041.new_terminal n hn
  · exact Paid16GeneralH042.new_terminal n hn
  · exact Paid16GeneralH043.new_terminal n hn
  · exact Paid16GeneralH044.new_terminal n hn
  · exact Paid16GeneralH045.new_terminal n hn
  · exact Paid16GeneralH046.new_terminal n hn
  · exact Paid16GeneralH047.new_terminal n hn
  · exact Paid16GeneralH048.new_terminal n hn
  · exact Paid16GeneralH049.new_terminal n hn
  · exact Paid16GeneralH050.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH041.newIDs ∨ n ∈ Paid16GeneralH042.newIDs ∨ n ∈ Paid16GeneralH043.newIDs ∨ n ∈ Paid16GeneralH044.newIDs ∨ n ∈ Paid16GeneralH045.newIDs ∨ n ∈ Paid16GeneralH046.newIDs ∨ n ∈ Paid16GeneralH047.newIDs ∨ n ∈ Paid16GeneralH048.newIDs ∨ n ∈ Paid16GeneralH049.newIDs ∨ n ∈ Paid16GeneralH050.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH041.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH042.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH043.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH044.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH045.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH046.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH047.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH048.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH049.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH050.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg05
#print axioms N11Formalization.Paid16GeneralHAgg05.new_radius
