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
private theorem of_all_le {s : Finset (Fin 5011)} {hi : ℕ}
    (h : (s.all fun n => n.val ≤ hi) = true) :
    ∀ n, n ∈ s → n.val ≤ hi := by
  intro n hn
  exact (Finset.all_eq_true.mp h) n hn
private theorem of_all_ge {s : Finset (Fin 5011)} {lo : ℕ}
    (h : (s.all fun n => lo ≤ n.val) = true) :
    ∀ n, n ∈ s → lo ≤ n.val := by
  intro n hn
  exact (Finset.all_eq_true.mp h) n hn
private theorem s01_bounds : ∀ n, n ∈ Paid16GeneralNext1182S01.newIDs →
    2565 ≤ n.val ∧ n.val ≤ 2736 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S01.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S01.newIDs) (by decide +kernel) n hn⟩
private theorem s02_bounds : ∀ n, n ∈ Paid16GeneralNext1182S02.newIDs →
    2737 ≤ n.val ∧ n.val ≤ 2906 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S02.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S02.newIDs) (by decide +kernel) n hn⟩
private theorem s03_bounds : ∀ n, n ∈ Paid16GeneralNext1182S03.newIDs →
    2907 ≤ n.val ∧ n.val ≤ 3087 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S03.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S03.newIDs) (by decide +kernel) n hn⟩
private theorem s04_bounds : ∀ n, n ∈ Paid16GeneralNext1182S04.newIDs →
    3088 ≤ n.val ∧ n.val ≤ 3266 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S04.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S04.newIDs) (by decide +kernel) n hn⟩
private theorem s05_bounds : ∀ n, n ∈ Paid16GeneralNext1182S05.newIDs →
    3267 ≤ n.val ∧ n.val ≤ 3445 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S05.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S05.newIDs) (by decide +kernel) n hn⟩
private theorem s06_bounds : ∀ n, n ∈ Paid16GeneralNext1182S06.newIDs →
    3446 ≤ n.val ∧ n.val ≤ 3954 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S06.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S06.newIDs) (by decide +kernel) n hn⟩
private theorem s07_bounds : ∀ n, n ∈ Paid16GeneralNext1182S07.newIDs →
    3955 ≤ n.val ∧ n.val ≤ 4984 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S07.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S07.newIDs) (by decide +kernel) n hn⟩
private theorem s08_bounds : ∀ n, n ∈ Paid16GeneralNext1182S08.newIDs →
    4986 ≤ n.val ∧ n.val ≤ 5007 := by
  intro n hn
  exact ⟨of_all_ge (s := Paid16GeneralNext1182S08.newIDs) (by decide +kernel) n hn,
    of_all_le (s := Paid16GeneralNext1182S08.newIDs) (by decide +kernel) n hn⟩
private theorem disjoint_s01_s02 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S02.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s01_bounds n hi
  have bj := s02_bounds n hj
  omega
private theorem disjoint_s01_s03 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S03.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s01_bounds n hi
  have bj := s03_bounds n hj
  omega
private theorem disjoint_s01_s04 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S04.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s01_bounds n hi
  have bj := s04_bounds n hj
  omega
private theorem disjoint_s01_s05 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s01_bounds n hi
  have bj := s05_bounds n hj
  omega
private theorem disjoint_s01_s06 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s01_bounds n hi
  have bj := s06_bounds n hj
  omega
private theorem disjoint_s01_s07 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s01_bounds n hi
  have bj := s07_bounds n hj
  omega
private theorem disjoint_s01_s08 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s01_bounds n hi
  have bj := s08_bounds n hj
  omega
private theorem disjoint_s02_s03 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S03.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s02_bounds n hi
  have bj := s03_bounds n hj
  omega
private theorem disjoint_s02_s04 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S04.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s02_bounds n hi
  have bj := s04_bounds n hj
  omega
private theorem disjoint_s02_s05 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s02_bounds n hi
  have bj := s05_bounds n hj
  omega
private theorem disjoint_s02_s06 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s02_bounds n hi
  have bj := s06_bounds n hj
  omega
private theorem disjoint_s02_s07 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s02_bounds n hi
  have bj := s07_bounds n hj
  omega
private theorem disjoint_s02_s08 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s02_bounds n hi
  have bj := s08_bounds n hj
  omega
private theorem disjoint_s03_s04 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S04.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s03_bounds n hi
  have bj := s04_bounds n hj
  omega
private theorem disjoint_s03_s05 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s03_bounds n hi
  have bj := s05_bounds n hj
  omega
private theorem disjoint_s03_s06 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s03_bounds n hi
  have bj := s06_bounds n hj
  omega
private theorem disjoint_s03_s07 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s03_bounds n hi
  have bj := s07_bounds n hj
  omega
private theorem disjoint_s03_s08 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s03_bounds n hi
  have bj := s08_bounds n hj
  omega
private theorem disjoint_s04_s05 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s04_bounds n hi
  have bj := s05_bounds n hj
  omega
private theorem disjoint_s04_s06 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s04_bounds n hi
  have bj := s06_bounds n hj
  omega
private theorem disjoint_s04_s07 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s04_bounds n hi
  have bj := s07_bounds n hj
  omega
private theorem disjoint_s04_s08 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s04_bounds n hi
  have bj := s08_bounds n hj
  omega
private theorem disjoint_s05_s06 : Disjoint Paid16GeneralNext1182S05.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s05_bounds n hi
  have bj := s06_bounds n hj
  omega
private theorem disjoint_s05_s07 : Disjoint Paid16GeneralNext1182S05.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s05_bounds n hi
  have bj := s07_bounds n hj
  omega
private theorem disjoint_s05_s08 : Disjoint Paid16GeneralNext1182S05.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s05_bounds n hi
  have bj := s08_bounds n hj
  omega
private theorem disjoint_s06_s07 : Disjoint Paid16GeneralNext1182S06.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s06_bounds n hi
  have bj := s07_bounds n hj
  omega
private theorem disjoint_s06_s08 : Disjoint Paid16GeneralNext1182S06.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s06_bounds n hi
  have bj := s08_bounds n hj
  omega
private theorem disjoint_s07_s08 : Disjoint Paid16GeneralNext1182S07.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s07_bounds n hi
  have bj := s08_bounds n hj
  omega
theorem new_count : newIDs.card = 1182 := by
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 8)) part := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [part, disjoint_s01_s02, disjoint_s01_s03, disjoint_s01_s04, disjoint_s01_s05, disjoint_s01_s06, disjoint_s01_s07, disjoint_s01_s08, disjoint_s02_s03, disjoint_s02_s04, disjoint_s02_s05, disjoint_s02_s06, disjoint_s02_s07, disjoint_s02_s08, disjoint_s03_s04, disjoint_s03_s05, disjoint_s03_s06, disjoint_s03_s07, disjoint_s03_s08, disjoint_s04_s05, disjoint_s04_s06, disjoint_s04_s07, disjoint_s04_s08, disjoint_s05_s06, disjoint_s05_s07, disjoint_s05_s08, disjoint_s06_s07, disjoint_s06_s08, disjoint_s07_s08]
  rw [newIDs, Finset.card_biUnion hdisj]
  simp only [Fin.sum_univ_eight, part,
      Paid16GeneralNext1182S01.new_count,
      Paid16GeneralNext1182S02.new_count,
      Paid16GeneralNext1182S03.new_count,
      Paid16GeneralNext1182S04.new_count,
      Paid16GeneralNext1182S05.new_count,
      Paid16GeneralNext1182S06.new_count,
      Paid16GeneralNext1182S07.new_count,
      Paid16GeneralNext1182S08.new_count]
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
