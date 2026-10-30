import N11Formalization.Paid16GeneralG01
import N11Formalization.Paid16GeneralG02
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

/-! Bounded descent facts used by B13. Image-valued blocks are decoded by
`mem_image` and `fin_cases`; B09 is classified through its nine union/insert
layers, and the 210-id remainder is assembled from ten 21-id blocks. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13DescentBounds
open Finset
noncomputable section

private theorem g01_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG01.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG01.nodeID]

private theorem g02_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG02.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG02.nodeID]

private theorem g03_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG03.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG03.nodeID]

private theorem g04_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG04.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG04.nodeID]

private theorem g05_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG05.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG05.nodeID]

private theorem g06_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG06.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG06.nodeID]

private theorem g07_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG07.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG07.nodeID]

private theorem g08_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG08.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG08.nodeID]

private theorem g09_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG09.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG09.nodeID]

private theorem g10_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG10.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG10.nodeID]

private theorem g11_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG11.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG11.nodeID]

private theorem g12_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralG12.newIDs) :
    n.val < 2565 := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16GeneralG12.nodeID]

/-- B09 is not wholly below 2565: `b09HighIDs` lists its 27 legacy ids at or
above 2565.  This exhaustive classification replaces the false former `b09_lt`
statement. -/
def b09HighIDs : Finset (Fin 5011) := {2661,2675,2880,2888,2962,2971,2973,3121,3134,3436,3591,3601,3619,3833,3834,3842,3852,3874,3950,3965,4058,4179,4265,4266,4267,4348,4485}

private theorem dispatch_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalDispatch.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalDispatch.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · have h : n = 284 ∨ n = 562 ∨ n = 4348 := by
      simpa only [EnergyCommonChart.paidEnergyIDs, Finset.mem_insert,
        Finset.mem_singleton] using hn
    rcases h with rfl | rfl | rfl <;> simp [b09HighIDs]
  · simp only [Finset.mem_singleton] at hn
    rcases hn with rfl
    simp [b09HighIDs]

private theorem lambda0_bound (n : Fin 5011)
    (hn : n ∈ Lambda0Batch7Consumer.newIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Lambda0Batch7Packet.nodeID, b09HighIDs]

private theorem chord_bound (n : Fin 5011)
    (hn : n ∈ Lambda0TangentChordC01Consumer.newIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Lambda0TangentChordC01Packet.nodeID, b09HighIDs]

private theorem cutting_bound (n : Fin 5011)
    (hn : n ∈ CuttingPlaneBatch7Consumer.newIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [CuttingPlaneBatch7Packet.nodeID, b09HighIDs]

private theorem batch22_bound (n : Fin 5011)
    (hn : n ∈ Paid16Batch22Consumer.newIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩
  fin_cases i <;> simp [Paid16Batch22Packet.nodeID, b09HighIDs]

private theorem b01_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB01.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB01.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact dispatch_bound n hn
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl <;> simp [b09HighIDs]

private theorem b02_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB02.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB02.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b01_bound n hn
  · simp only [Finset.mem_singleton] at hn
    rcases hn with rfl
    simp [b09HighIDs]

private theorem b03_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB03.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB03.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b02_bound n hn
  · exact lambda0_bound n hn

private theorem b04_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB04.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB04.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b03_bound n hn
  · exact chord_bound n hn

private theorem b05_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB05.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB05.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b04_bound n hn
  · exact cutting_bound n hn

private theorem b06_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB06.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB06.paidIDs] at hn
  rcases Finset.mem_insert.mp hn with rfl | hn
  · simp [b09HighIDs]
  · exact b05_bound n hn

private theorem b07_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB07.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB07.paidIDs] at hn
  rcases Finset.mem_insert.mp hn with rfl | hn
  · simp [b09HighIDs]
  · rcases Finset.mem_insert.mp hn with rfl | hn
    · simp [b09HighIDs]
    · exact b06_bound n hn

private theorem b08_bound (n : Fin 5011)
    (hn : n ∈ EnergyTerminalBatchB08.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB08.paidIDs] at hn
  rcases Finset.mem_insert.mp hn with rfl | hn
  · simp [b09HighIDs]
  · exact b07_bound n hn

theorem b09_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB09.paidIDs) :
    n.val < 2565 ∨ n ∈ b09HighIDs := by
  rw [EnergyTerminalBatchB09.paidIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact b08_bound n hn
  · exact batch22_bound n hn

theorem first42_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralFirst42.newIDs) :
    n.val < 2565 := by
  rw [Paid16GeneralFirst42.newIDs] at hn
  rcases Finset.mem_union.mp hn with hn | hn
  · exact g01_lt n hn
  · exact g02_lt n hn

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
