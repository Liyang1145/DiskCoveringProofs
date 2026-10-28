import N11Formalization.Paid16GeneralNext1182S01
import N11Formalization.Paid16GeneralNext1182S02
import N11Formalization.Paid16GeneralNext1182S03
import N11Formalization.Paid16GeneralNext1182S04
import N11Formalization.Paid16GeneralNext1182S05
import N11Formalization.Paid16GeneralNext1182S06
import N11Formalization.Paid16GeneralNext1182S07
import N11Formalization.Paid16GeneralNext1182S08

import N11Formalization.EnergyTerminalBatchB12

/-! Top aggregate of 1182 packets, assembled from 8 sub-aggregates.
Every `decide +kernel` here compares at most 168-element literal sets, so the
kernel never walks a >168-deep insert chain. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.Paid16GeneralNext1182
open Finset
noncomputable section

def newIDs : Finset (Fin 5011) := Paid16GeneralNext1182S01.newIDs ∪ (Paid16GeneralNext1182S02.newIDs ∪ (Paid16GeneralNext1182S03.newIDs ∪ (Paid16GeneralNext1182S04.newIDs ∪ (Paid16GeneralNext1182S05.newIDs ∪ (Paid16GeneralNext1182S06.newIDs ∪ (Paid16GeneralNext1182S07.newIDs ∪ (Paid16GeneralNext1182S08.newIDs)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ Paid16GeneralNext1182S01.newIDs ∨ n ∈ Paid16GeneralNext1182S02.newIDs ∨ n ∈ Paid16GeneralNext1182S03.newIDs ∨ n ∈ Paid16GeneralNext1182S04.newIDs ∨ n ∈ Paid16GeneralNext1182S05.newIDs ∨ n ∈ Paid16GeneralNext1182S06.newIDs ∨ n ∈ Paid16GeneralNext1182S07.newIDs ∨ n ∈ Paid16GeneralNext1182S08.newIDs := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 1182 := by
  have d0 : Disjoint Paid16GeneralNext1182S01.newIDs (Paid16GeneralNext1182S08.newIDs ∪ (Paid16GeneralNext1182S07.newIDs ∪ (Paid16GeneralNext1182S06.newIDs ∪ (Paid16GeneralNext1182S05.newIDs ∪ (Paid16GeneralNext1182S04.newIDs ∪ (Paid16GeneralNext1182S03.newIDs ∪ (Paid16GeneralNext1182S02.newIDs))))))) := by decide +kernel
  have d1 : Disjoint Paid16GeneralNext1182S02.newIDs (Paid16GeneralNext1182S08.newIDs ∪ (Paid16GeneralNext1182S07.newIDs ∪ (Paid16GeneralNext1182S06.newIDs ∪ (Paid16GeneralNext1182S05.newIDs ∪ (Paid16GeneralNext1182S04.newIDs ∪ (Paid16GeneralNext1182S03.newIDs)))))) := by decide +kernel
  have d2 : Disjoint Paid16GeneralNext1182S03.newIDs (Paid16GeneralNext1182S08.newIDs ∪ (Paid16GeneralNext1182S07.newIDs ∪ (Paid16GeneralNext1182S06.newIDs ∪ (Paid16GeneralNext1182S05.newIDs ∪ (Paid16GeneralNext1182S04.newIDs))))) := by decide +kernel
  have d3 : Disjoint Paid16GeneralNext1182S04.newIDs (Paid16GeneralNext1182S08.newIDs ∪ (Paid16GeneralNext1182S07.newIDs ∪ (Paid16GeneralNext1182S06.newIDs ∪ (Paid16GeneralNext1182S05.newIDs)))) := by decide +kernel
  have d4 : Disjoint Paid16GeneralNext1182S05.newIDs (Paid16GeneralNext1182S08.newIDs ∪ (Paid16GeneralNext1182S07.newIDs ∪ (Paid16GeneralNext1182S06.newIDs))) := by decide +kernel
  have d5 : Disjoint Paid16GeneralNext1182S06.newIDs (Paid16GeneralNext1182S08.newIDs ∪ (Paid16GeneralNext1182S07.newIDs)) := by decide +kernel
  have d6 : Disjoint Paid16GeneralNext1182S07.newIDs (Paid16GeneralNext1182S08.newIDs) := by decide +kernel
  rw [newIDs]
  rw [Finset.card_union_of_disjoint d0, Paid16GeneralNext1182S01.new_count]
  rw [Finset.card_union_of_disjoint d1, Paid16GeneralNext1182S02.new_count]
  rw [Finset.card_union_of_disjoint d2, Paid16GeneralNext1182S03.new_count]
  rw [Finset.card_union_of_disjoint d3, Paid16GeneralNext1182S04.new_count]
  rw [Finset.card_union_of_disjoint d4, Paid16GeneralNext1182S05.new_count]
  rw [Finset.card_union_of_disjoint d5, Paid16GeneralNext1182S06.new_count]
  rw [Finset.card_union_of_disjoint d6, Paid16GeneralNext1182S07.new_count]
  rw [Paid16GeneralNext1182S08.new_count]
  norm_num
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralNext1182S01.new_terminal n h
  · exact Paid16GeneralNext1182S02.new_terminal n h
  · exact Paid16GeneralNext1182S03.new_terminal n h
  · exact Paid16GeneralNext1182S04.new_terminal n h
  · exact Paid16GeneralNext1182S05.new_terminal n h
  · exact Paid16GeneralNext1182S06.new_terminal n h
  · exact Paid16GeneralNext1182S07.new_terminal n h
  · exact Paid16GeneralNext1182S08.new_terminal n h
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralNext1182S01.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S02.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S03.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S04.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S05.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S06.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S07.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S08.new_radius n h y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rcases (new_mem a).mp ha with h | h | h | h | h | h | h | h
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S01.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S02.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S03.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S04.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S05.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S06.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S07.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S08.disjoint_sharp) (a := a) h hb
end
end N11Formalization.Paid16GeneralNext1182
#check @N11Formalization.Paid16GeneralNext1182.new_count
#print axioms N11Formalization.Paid16GeneralNext1182.new_count
#print axioms N11Formalization.Paid16GeneralNext1182.new_radius
#print axioms N11Formalization.Paid16GeneralNext1182.new_terminal
