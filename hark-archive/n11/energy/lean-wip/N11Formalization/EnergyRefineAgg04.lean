import N11Formalization.EnergyRefineN3777
import N11Formalization.EnergyRefineN3778
import N11Formalization.EnergyRefineN3781
import N11Formalization.EnergyRefineN3783
import N11Formalization.EnergyRefineN3792
import N11Formalization.EnergyRefineN3794
import N11Formalization.EnergyRefineN3795
import N11Formalization.EnergyRefineN3800
import N11Formalization.EnergyRefineN3802
import N11Formalization.EnergyRefineN3803
/-! Generated aggregation (NOT compiled, NOT paid). -/
set_option autoImplicit false
namespace N11Formalization.EnergyRefineAgg04
open Finset
noncomputable section
set_option maxRecDepth 10000
def newIDs : Finset (Fin 5011) := EnergyRefineN3777.newIDs ∪ (EnergyRefineN3778.newIDs ∪ (EnergyRefineN3781.newIDs ∪ (EnergyRefineN3783.newIDs ∪ (EnergyRefineN3792.newIDs ∪ (EnergyRefineN3794.newIDs ∪ (EnergyRefineN3795.newIDs ∪ (EnergyRefineN3800.newIDs ∪ (EnergyRefineN3802.newIDs ∪ (EnergyRefineN3803.newIDs)))))))))
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have hm : n ∈ EnergyRefineN3777.newIDs ∨ n ∈ EnergyRefineN3778.newIDs ∨ n ∈ EnergyRefineN3781.newIDs ∨ n ∈ EnergyRefineN3783.newIDs ∨ n ∈ EnergyRefineN3792.newIDs ∨ n ∈ EnergyRefineN3794.newIDs ∨ n ∈ EnergyRefineN3795.newIDs ∨ n ∈ EnergyRefineN3800.newIDs ∨ n ∈ EnergyRefineN3802.newIDs ∨ n ∈ EnergyRefineN3803.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3777.new_terminal n hn
  · exact EnergyRefineN3778.new_terminal n hn
  · exact EnergyRefineN3781.new_terminal n hn
  · exact EnergyRefineN3783.new_terminal n hn
  · exact EnergyRefineN3792.new_terminal n hn
  · exact EnergyRefineN3794.new_terminal n hn
  · exact EnergyRefineN3795.new_terminal n hn
  · exact EnergyRefineN3800.new_terminal n hn
  · exact EnergyRefineN3802.new_terminal n hn
  · exact EnergyRefineN3803.new_terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hm : n ∈ EnergyRefineN3777.newIDs ∨ n ∈ EnergyRefineN3778.newIDs ∨ n ∈ EnergyRefineN3781.newIDs ∨ n ∈ EnergyRefineN3783.newIDs ∨ n ∈ EnergyRefineN3792.newIDs ∨ n ∈ EnergyRefineN3794.newIDs ∨ n ∈ EnergyRefineN3795.newIDs ∨ n ∈ EnergyRefineN3800.newIDs ∨ n ∈ EnergyRefineN3802.newIDs ∨ n ∈ EnergyRefineN3803.newIDs := by
    simpa only [newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact EnergyRefineN3777.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3778.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3781.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3783.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3792.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3794.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3795.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3800.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3802.new_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN3803.new_radius n hn y hy0 hy1 hc C Z r hf
end
end N11Formalization.EnergyRefineAgg04
#print axioms N11Formalization.EnergyRefineAgg04.new_radius
