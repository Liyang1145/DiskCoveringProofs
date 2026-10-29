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
namespace N11Formalization.Paid16GeneralNext1182
open Finset
noncomputable section

def part : Fin 8 → Finset (Fin 5011)
  | 0 => Paid16GeneralNext1182S01.newIDs
  | 1 => Paid16GeneralNext1182S02.newIDs
  | 2 => Paid16GeneralNext1182S03.newIDs
  | 3 => Paid16GeneralNext1182S04.newIDs
  | 4 => Paid16GeneralNext1182S05.newIDs
  | 5 => Paid16GeneralNext1182S06.newIDs
  | 6 => Paid16GeneralNext1182S07.newIDs
  | 7 => Paid16GeneralNext1182S08.newIDs
def newIDs : Finset (Fin 5011) := Finset.univ.biUnion part
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ Paid16GeneralNext1182S01.newIDs ∨ n ∈ Paid16GeneralNext1182S02.newIDs ∨ n ∈ Paid16GeneralNext1182S03.newIDs ∨ n ∈ Paid16GeneralNext1182S04.newIDs ∨ n ∈ Paid16GeneralNext1182S05.newIDs ∨ n ∈ Paid16GeneralNext1182S06.newIDs ∨ n ∈ Paid16GeneralNext1182S07.newIDs ∨ n ∈ Paid16GeneralNext1182S08.newIDs := by
  simp only [newIDs, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [part]
  · rintro (h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7)
    · exact ⟨0, by simpa [part] using h0⟩
    · exact ⟨1, by simpa [part] using h1⟩
    · exact ⟨2, by simpa [part] using h2⟩
    · exact ⟨3, by simpa [part] using h3⟩
    · exact ⟨4, by simpa [part] using h4⟩
    · exact ⟨5, by simpa [part] using h5⟩
    · exact ⟨6, by simpa [part] using h6⟩
    · exact ⟨7, by simpa [part] using h7⟩
theorem new_count : newIDs.card = 1182 := by
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 8)) part := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [part] <;> decide +kernel
  rw [newIDs, Finset.card_biUnion hdisj]
  simp only [part,
      Paid16GeneralNext1182S01.new_count,
      Paid16GeneralNext1182S02.new_count,
      Paid16GeneralNext1182S03.new_count,
      Paid16GeneralNext1182S04.new_count,
      Paid16GeneralNext1182S05.new_count,
      Paid16GeneralNext1182S06.new_count,
      Paid16GeneralNext1182S07.new_count,
      Paid16GeneralNext1182S08.new_count]
  decide +kernel
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
