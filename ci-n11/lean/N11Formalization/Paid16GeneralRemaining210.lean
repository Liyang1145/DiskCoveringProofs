import N11Formalization.Paid16GeneralG03
import N11Formalization.Paid16GeneralG04
import N11Formalization.Paid16GeneralG05
import N11Formalization.Paid16GeneralG06
import N11Formalization.Paid16GeneralG07
import N11Formalization.Paid16GeneralG08
import N11Formalization.Paid16GeneralG09
import N11Formalization.Paid16GeneralG10
import N11Formalization.Paid16GeneralG11
import N11Formalization.Paid16GeneralG12
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralRemaining210
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralG03.newIDs ∪ (Paid16GeneralG04.newIDs ∪ (Paid16GeneralG05.newIDs ∪ (Paid16GeneralG06.newIDs ∪ (Paid16GeneralG07.newIDs ∪ (Paid16GeneralG08.newIDs ∪ (Paid16GeneralG09.newIDs ∪ (Paid16GeneralG10.newIDs ∪ (Paid16GeneralG11.newIDs ∪ (Paid16GeneralG12.newIDs)))))))))
theorem new_count : newIDs.card = 210 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralG03.newIDs ∨ n ∈ Paid16GeneralG04.newIDs ∨ n ∈ Paid16GeneralG05.newIDs ∨ n ∈ Paid16GeneralG06.newIDs ∨ n ∈ Paid16GeneralG07.newIDs ∨ n ∈ Paid16GeneralG08.newIDs ∨ n ∈ Paid16GeneralG09.newIDs ∨ n ∈ Paid16GeneralG10.newIDs ∨ n ∈ Paid16GeneralG11.newIDs ∨ n ∈ Paid16GeneralG12.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralG03.new_terminal n hn
  · exact Paid16GeneralG04.new_terminal n hn
  · exact Paid16GeneralG05.new_terminal n hn
  · exact Paid16GeneralG06.new_terminal n hn
  · exact Paid16GeneralG07.new_terminal n hn
  · exact Paid16GeneralG08.new_terminal n hn
  · exact Paid16GeneralG09.new_terminal n hn
  · exact Paid16GeneralG10.new_terminal n hn
  · exact Paid16GeneralG11.new_terminal n hn
  · exact Paid16GeneralG12.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralG03.newIDs ∨ n ∈ Paid16GeneralG04.newIDs ∨ n ∈ Paid16GeneralG05.newIDs ∨ n ∈ Paid16GeneralG06.newIDs ∨ n ∈ Paid16GeneralG07.newIDs ∨ n ∈ Paid16GeneralG08.newIDs ∨ n ∈ Paid16GeneralG09.newIDs ∨ n ∈ Paid16GeneralG10.newIDs ∨ n ∈ Paid16GeneralG11.newIDs ∨ n ∈ Paid16GeneralG12.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralG03.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG04.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG05.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG06.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG07.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG08.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG09.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG10.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG11.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralG12.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralRemaining210
#check @N11Formalization.Paid16GeneralRemaining210.new_count
#check @N11Formalization.Paid16GeneralRemaining210.new_radius
#print axioms N11Formalization.Paid16GeneralRemaining210.new_radius
