import N11Formalization.Paid16GeneralH82

/-! Sub-aggregate 8/8: 1 packet modules, 6 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext1182S08
open Finset
noncomputable section

def ids56 : Finset (Fin 5011) := {4986,4990,4995,5000,5002,5007}
theorem mem_ids56 (n : Fin 5011) : n ∈ ids56 ↔ n = 4986 ∨ n = 4990 ∨ n = 4995 ∨ n = 5000 ∨ n = 5002 ∨ n = 5007 := by
  simp only [ids56, Finset.mem_insert, Finset.mem_singleton]
theorem ids56_card : ids56.card = 6 := by decide +kernel
theorem sub56 (n : Fin 5011) (hn : n ∈ ids56) : n ∈ Paid16GeneralH82.newIDs := by
  rcases (mem_ids56 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
def newIDs : Finset (Fin 5011) := ids56
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids56 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 6 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h
  · exact Paid16GeneralH82.new_terminal n (sub56 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h
  · exact Paid16GeneralH82.new_radius n (sub56 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S08
#print axioms N11Formalization.Paid16GeneralNext1182S08.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S08.new_radius
