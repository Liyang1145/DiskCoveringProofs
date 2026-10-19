import N11Formalization.Paid16GeneralHAgg01
import N11Formalization.Paid16GeneralHAgg02
import N11Formalization.Paid16GeneralHAgg03
import N11Formalization.Paid16GeneralHAgg04
import N11Formalization.Paid16GeneralHAgg05
import N11Formalization.Paid16GeneralHAgg06
import N11Formalization.Paid16GeneralHAgg07
import N11Formalization.Paid16GeneralHAgg08
import N11Formalization.Paid16GeneralHAgg09
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAll
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralHAgg01.newIDs ∪ (Paid16GeneralHAgg02.newIDs ∪ (Paid16GeneralHAgg03.newIDs ∪ (Paid16GeneralHAgg04.newIDs ∪ (Paid16GeneralHAgg05.newIDs ∪ (Paid16GeneralHAgg06.newIDs ∪ (Paid16GeneralHAgg07.newIDs ∪ (Paid16GeneralHAgg08.newIDs ∪ (Paid16GeneralHAgg09.newIDs))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralHAgg01.newIDs ∨ n ∈ Paid16GeneralHAgg02.newIDs ∨ n ∈ Paid16GeneralHAgg03.newIDs ∨ n ∈ Paid16GeneralHAgg04.newIDs ∨ n ∈ Paid16GeneralHAgg05.newIDs ∨ n ∈ Paid16GeneralHAgg06.newIDs ∨ n ∈ Paid16GeneralHAgg07.newIDs ∨ n ∈ Paid16GeneralHAgg08.newIDs ∨ n ∈ Paid16GeneralHAgg09.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralHAgg01.new_terminal n hn
  · exact Paid16GeneralHAgg02.new_terminal n hn
  · exact Paid16GeneralHAgg03.new_terminal n hn
  · exact Paid16GeneralHAgg04.new_terminal n hn
  · exact Paid16GeneralHAgg05.new_terminal n hn
  · exact Paid16GeneralHAgg06.new_terminal n hn
  · exact Paid16GeneralHAgg07.new_terminal n hn
  · exact Paid16GeneralHAgg08.new_terminal n hn
  · exact Paid16GeneralHAgg09.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralHAgg01.newIDs ∨ n ∈ Paid16GeneralHAgg02.newIDs ∨ n ∈ Paid16GeneralHAgg03.newIDs ∨ n ∈ Paid16GeneralHAgg04.newIDs ∨ n ∈ Paid16GeneralHAgg05.newIDs ∨ n ∈ Paid16GeneralHAgg06.newIDs ∨ n ∈ Paid16GeneralHAgg07.newIDs ∨ n ∈ Paid16GeneralHAgg08.newIDs ∨ n ∈ Paid16GeneralHAgg09.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralHAgg01.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg02.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg03.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg04.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg05.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg06.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg07.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg08.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralHAgg09.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAll
#print axioms N11Formalization.Paid16GeneralHAll.new_radius
