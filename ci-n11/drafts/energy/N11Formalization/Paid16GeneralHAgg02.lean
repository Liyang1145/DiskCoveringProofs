import N11Formalization.Paid16GeneralH011
import N11Formalization.Paid16GeneralH012
import N11Formalization.Paid16GeneralH013
import N11Formalization.Paid16GeneralH014
import N11Formalization.Paid16GeneralH015
import N11Formalization.Paid16GeneralH016
import N11Formalization.Paid16GeneralH017
import N11Formalization.Paid16GeneralH018
import N11Formalization.Paid16GeneralH019
import N11Formalization.Paid16GeneralH020
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralHAgg02
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := Paid16GeneralH011.newIDs ∪ (Paid16GeneralH012.newIDs ∪ (Paid16GeneralH013.newIDs ∪ (Paid16GeneralH014.newIDs ∪ (Paid16GeneralH015.newIDs ∪ (Paid16GeneralH016.newIDs ∪ (Paid16GeneralH017.newIDs ∪ (Paid16GeneralH018.newIDs ∪ (Paid16GeneralH019.newIDs ∪ (Paid16GeneralH020.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ Paid16GeneralH011.newIDs ∨ n ∈ Paid16GeneralH012.newIDs ∨ n ∈ Paid16GeneralH013.newIDs ∨ n ∈ Paid16GeneralH014.newIDs ∨ n ∈ Paid16GeneralH015.newIDs ∨ n ∈ Paid16GeneralH016.newIDs ∨ n ∈ Paid16GeneralH017.newIDs ∨ n ∈ Paid16GeneralH018.newIDs ∨ n ∈ Paid16GeneralH019.newIDs ∨ n ∈ Paid16GeneralH020.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH011.new_terminal n hn
  · exact Paid16GeneralH012.new_terminal n hn
  · exact Paid16GeneralH013.new_terminal n hn
  · exact Paid16GeneralH014.new_terminal n hn
  · exact Paid16GeneralH015.new_terminal n hn
  · exact Paid16GeneralH016.new_terminal n hn
  · exact Paid16GeneralH017.new_terminal n hn
  · exact Paid16GeneralH018.new_terminal n hn
  · exact Paid16GeneralH019.new_terminal n hn
  · exact Paid16GeneralH020.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ Paid16GeneralH011.newIDs ∨ n ∈ Paid16GeneralH012.newIDs ∨ n ∈ Paid16GeneralH013.newIDs ∨ n ∈ Paid16GeneralH014.newIDs ∨ n ∈ Paid16GeneralH015.newIDs ∨ n ∈ Paid16GeneralH016.newIDs ∨ n ∈ Paid16GeneralH017.newIDs ∨ n ∈ Paid16GeneralH018.newIDs ∨ n ∈ Paid16GeneralH019.newIDs ∨ n ∈ Paid16GeneralH020.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact Paid16GeneralH011.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH012.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH013.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH014.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH015.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH016.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH017.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH018.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH019.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH020.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.Paid16GeneralHAgg02
#print axioms N11Formalization.Paid16GeneralHAgg02.new_radius
