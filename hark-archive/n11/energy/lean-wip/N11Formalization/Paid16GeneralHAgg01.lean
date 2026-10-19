import N11Formalization.Paid16GeneralH001
import N11Formalization.Paid16GeneralH002
import N11Formalization.Paid16GeneralH003
import N11Formalization.Paid16GeneralH004
import N11Formalization.Paid16GeneralH005
import N11Formalization.Paid16GeneralH006
import N11Formalization.Paid16GeneralH007
import N11Formalization.Paid16GeneralH008
import N11Formalization.Paid16GeneralH009
import N11Formalization.Paid16GeneralH010
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg01
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH001.newIDs ∪ (Paid16GeneralH002.newIDs ∪ (Paid16GeneralH003.newIDs ∪ (Paid16GeneralH004.newIDs ∪ (Paid16GeneralH005.newIDs ∪ (Paid16GeneralH006.newIDs ∪ (Paid16GeneralH007.newIDs ∪ (Paid16GeneralH008.newIDs ∪ (Paid16GeneralH009.newIDs ∪ (Paid16GeneralH010.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH001.newIDs ∨ n ∈ Paid16GeneralH002.newIDs ∨ n ∈ Paid16GeneralH003.newIDs ∨ n ∈ Paid16GeneralH004.newIDs ∨ n ∈ Paid16GeneralH005.newIDs ∨ n ∈ Paid16GeneralH006.newIDs ∨ n ∈ Paid16GeneralH007.newIDs ∨ n ∈ Paid16GeneralH008.newIDs ∨ n ∈ Paid16GeneralH009.newIDs ∨ n ∈ Paid16GeneralH010.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH001.new_terminal n hn
  · exact Paid16GeneralH002.new_terminal n hn
  · exact Paid16GeneralH003.new_terminal n hn
  · exact Paid16GeneralH004.new_terminal n hn
  · exact Paid16GeneralH005.new_terminal n hn
  · exact Paid16GeneralH006.new_terminal n hn
  · exact Paid16GeneralH007.new_terminal n hn
  · exact Paid16GeneralH008.new_terminal n hn
  · exact Paid16GeneralH009.new_terminal n hn
  · exact Paid16GeneralH010.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH001.newIDs ∨ n ∈ Paid16GeneralH002.newIDs ∨ n ∈ Paid16GeneralH003.newIDs ∨ n ∈ Paid16GeneralH004.newIDs ∨ n ∈ Paid16GeneralH005.newIDs ∨ n ∈ Paid16GeneralH006.newIDs ∨ n ∈ Paid16GeneralH007.newIDs ∨ n ∈ Paid16GeneralH008.newIDs ∨ n ∈ Paid16GeneralH009.newIDs ∨ n ∈ Paid16GeneralH010.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH001.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH002.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH003.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH004.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH005.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH006.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH007.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH008.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH009.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH010.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg01
#print axioms N11Formalization.Paid16GeneralHAgg01.new_radius
