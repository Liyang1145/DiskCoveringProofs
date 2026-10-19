import N11Formalization.Paid16GeneralG01
import N11Formalization.Paid16GeneralG02
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralFirst42
open Finset
noncomputable section
def newIDs : Finset (Fin 5011) := Paid16GeneralG01.newIDs ∪ Paid16GeneralG02.newIDs
theorem groups_disjoint : Disjoint Paid16GeneralG01.newIDs Paid16GeneralG02.newIDs := by
  decide +kernel
theorem new_count : newIDs.card = 42 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact Paid16GeneralG01.new_terminal n hn
  · exact Paid16GeneralG02.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact Paid16GeneralG01.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG02.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralFirst42
#check @N11Formalization.Paid16GeneralFirst42.new_count
#check @N11Formalization.Paid16GeneralFirst42.new_radius
#print axioms N11Formalization.Paid16GeneralFirst42.new_radius
