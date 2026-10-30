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
import N11Formalization.EnergyTerminalBatchB10
import N11Formalization.Paid16GeneralRemaining210

/-! Bounded descent facts used by B13. Each kernel decision covers at most
58 literal ids; the 210-id remainder is assembled from ten 21-id blocks. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.EnergyTerminalBatchB13DescentBounds
open Finset
noncomputable section

private theorem g03_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG03.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG03.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g04_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG04.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG04.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g05_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG05.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG05.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g06_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG06.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG06.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g07_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG07.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG07.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g08_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG08.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG08.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g09_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG09.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG09.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g10_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG10.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG10.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g11_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG11.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG11.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

private theorem g12_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG12.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralG12.newIDs, m.val < 2565 := by decide +kernel
  exact h n hn

/-- B09 is not wholly below 2565: `b09HighIDs` lists its 27 legacy ids at or
above 2565.  This exhaustive classification replaces the false former `b09_lt`
statement. -/
def b09HighIDs : Finset (Fin 5011) := {2661,2675,2880,2888,2962,2971,2973,3121,3134,3436,3591,3601,3619,3833,3834,3842,3852,3874,3950,3965,4058,4179,4265,4266,4267,4348,4485}

theorem b09_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB09.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  have h : ∀ m ∈ EnergyTerminalBatchB09.paidIDs, m.val < 2565 ∨ m ∈ b09HighIDs := by
    decide +kernel
  exact h n hn

theorem first42_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralFirst42.newIDs) :
    n.val < 2565 := by
  have h : ∀ m ∈ Paid16GeneralFirst42.newIDs, m.val < 2565 := by
    decide +kernel
  exact h n hn

theorem b10_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB10.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB10.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b09_bound n hn
  · exact Or.inl (first42_lt n hn)

theorem remaining210_lt (n : Fin 5011)
    (hn : n ∈ Paid16GeneralRemaining210.newIDs) : n.val < 2565 := by
  have hm : n ∈ Paid16GeneralG03.newIDs ∨
      n ∈ Paid16GeneralG04.newIDs ∨
      n ∈ Paid16GeneralG05.newIDs ∨
      n ∈ Paid16GeneralG06.newIDs ∨
      n ∈ Paid16GeneralG07.newIDs ∨
      n ∈ Paid16GeneralG08.newIDs ∨
      n ∈ Paid16GeneralG09.newIDs ∨
      n ∈ Paid16GeneralG10.newIDs ∨
      n ∈ Paid16GeneralG11.newIDs ∨
      n ∈ Paid16GeneralG12.newIDs := by
    simpa only [Paid16GeneralRemaining210.newIDs, Finset.mem_union] using hn
  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  · exact g03_lt n hn
  · exact g04_lt n hn
  · exact g05_lt n hn
  · exact g06_lt n hn
  · exact g07_lt n hn
  · exact g08_lt n hn
  · exact g09_lt n hn
  · exact g10_lt n hn
  · exact g11_lt n hn
  · exact g12_lt n hn


theorem b11_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB11.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB11.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b10_bound n hn
  · exact Or.inl (remaining210_lt n hn)

/-- Every B09 id above 2565 is absent from the 57 literal Next1182 blocks. -/
theorem high_not_next (n : Fin 5011) (hn : n ∈ b09HighIDs) :
    n ∉ Paid16GeneralNext1182.newIDs := by
  simp only [b09HighIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h
  · rw [Paid16GeneralNext1182.new_mem]
    rintro (h | h | h | h | h | h | h | h)
    · simp only [Paid16GeneralNext1182S01.new_mem, Paid16GeneralNext1182S01.mem_ids00, Paid16GeneralNext1182S01.mem_ids01, Paid16GeneralNext1182S01.mem_ids02, Paid16GeneralNext1182S01.mem_ids03, Paid16GeneralNext1182S01.mem_ids04, Paid16GeneralNext1182S01.mem_ids05, Paid16GeneralNext1182S01.mem_ids06, Paid16GeneralNext1182S01.mem_ids07] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S02.new_mem, Paid16GeneralNext1182S02.mem_ids08, Paid16GeneralNext1182S02.mem_ids09, Paid16GeneralNext1182S02.mem_ids10, Paid16GeneralNext1182S02.mem_ids11, Paid16GeneralNext1182S02.mem_ids12, Paid16GeneralNext1182S02.mem_ids13, Paid16GeneralNext1182S02.mem_ids14, Paid16GeneralNext1182S02.mem_ids15] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S03.new_mem, Paid16GeneralNext1182S03.mem_ids16, Paid16GeneralNext1182S03.mem_ids17, Paid16GeneralNext1182S03.mem_ids18, Paid16GeneralNext1182S03.mem_ids19, Paid16GeneralNext1182S03.mem_ids20, Paid16GeneralNext1182S03.mem_ids21, Paid16GeneralNext1182S03.mem_ids22, Paid16GeneralNext1182S03.mem_ids23] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S04.new_mem, Paid16GeneralNext1182S04.mem_ids24, Paid16GeneralNext1182S04.mem_ids25, Paid16GeneralNext1182S04.mem_ids26, Paid16GeneralNext1182S04.mem_ids27, Paid16GeneralNext1182S04.mem_ids28, Paid16GeneralNext1182S04.mem_ids29, Paid16GeneralNext1182S04.mem_ids30, Paid16GeneralNext1182S04.mem_ids31] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S05.new_mem, Paid16GeneralNext1182S05.mem_ids32, Paid16GeneralNext1182S05.mem_ids33, Paid16GeneralNext1182S05.mem_ids34, Paid16GeneralNext1182S05.mem_ids35, Paid16GeneralNext1182S05.mem_ids36, Paid16GeneralNext1182S05.mem_ids37, Paid16GeneralNext1182S05.mem_ids38, Paid16GeneralNext1182S05.mem_ids39] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S06.new_mem, Paid16GeneralNext1182S06.mem_ids40, Paid16GeneralNext1182S06.mem_ids41, Paid16GeneralNext1182S06.mem_ids42, Paid16GeneralNext1182S06.mem_ids43, Paid16GeneralNext1182S06.mem_ids44, Paid16GeneralNext1182S06.mem_ids45, Paid16GeneralNext1182S06.mem_ids46, Paid16GeneralNext1182S06.mem_ids47] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S07.new_mem, Paid16GeneralNext1182S07.mem_ids48, Paid16GeneralNext1182S07.mem_ids49, Paid16GeneralNext1182S07.mem_ids50, Paid16GeneralNext1182S07.mem_ids51, Paid16GeneralNext1182S07.mem_ids52, Paid16GeneralNext1182S07.mem_ids53, Paid16GeneralNext1182S07.mem_ids54, Paid16GeneralNext1182S07.mem_ids55] at h
      norm_num at h
    · simp only [Paid16GeneralNext1182S08.new_mem, Paid16GeneralNext1182S08.mem_ids56] at h
      norm_num at h

end
end N11Formalization.EnergyTerminalBatchB13DescentBounds
#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.b09_bound
#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound
#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt
#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.b09_bound
#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound
#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt
