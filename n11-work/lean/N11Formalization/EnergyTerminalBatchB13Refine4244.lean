import N11Formalization.EnergyTerminalBatchB13
import N11Formalization.EnergyRefineN4244

/-! Refine the B13 paid set by the archived split certificate for source
terminal 4244.  The archive bytes are restored verbatim and remain CI
pending; the membership proof stays hierarchical. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13Refine4244
open Finset
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB13.paidIDs ∪ EnergyRefineN4244.newIDs

private theorem not_next1182_part01_ids00 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids00 := by
  decide +kernel
private theorem not_next1182_part01_ids01 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids01 := by
  decide +kernel
private theorem not_next1182_part01_ids02 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids02 := by
  decide +kernel
private theorem not_next1182_part01_ids03 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids03 := by
  decide +kernel
private theorem not_next1182_part01_ids04 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids04 := by
  decide +kernel
private theorem not_next1182_part01_ids05 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids05 := by
  decide +kernel
private theorem not_next1182_part01_ids06 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids06 := by
  decide +kernel
private theorem not_next1182_part01_ids07 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.ids07 := by
  decide +kernel
private theorem not_next1182_part01 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S01.newIDs := by
  rw [Paid16GeneralNext1182S01.new_mem]
  push_neg
  exact ⟨not_next1182_part01_ids00, not_next1182_part01_ids01, not_next1182_part01_ids02, not_next1182_part01_ids03, not_next1182_part01_ids04, not_next1182_part01_ids05, not_next1182_part01_ids06, not_next1182_part01_ids07⟩
private theorem not_next1182_part02_ids08 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids08 := by
  decide +kernel
private theorem not_next1182_part02_ids09 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids09 := by
  decide +kernel
private theorem not_next1182_part02_ids10 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids10 := by
  decide +kernel
private theorem not_next1182_part02_ids11 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids11 := by
  decide +kernel
private theorem not_next1182_part02_ids12 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids12 := by
  decide +kernel
private theorem not_next1182_part02_ids13 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids13 := by
  decide +kernel
private theorem not_next1182_part02_ids14 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids14 := by
  decide +kernel
private theorem not_next1182_part02_ids15 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.ids15 := by
  decide +kernel
private theorem not_next1182_part02 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S02.newIDs := by
  rw [Paid16GeneralNext1182S02.new_mem]
  push_neg
  exact ⟨not_next1182_part02_ids08, not_next1182_part02_ids09, not_next1182_part02_ids10, not_next1182_part02_ids11, not_next1182_part02_ids12, not_next1182_part02_ids13, not_next1182_part02_ids14, not_next1182_part02_ids15⟩
private theorem not_next1182_part03_ids16 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids16 := by decide +kernel
private theorem not_next1182_part03_ids17 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids17 := by decide +kernel
private theorem not_next1182_part03_ids18 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids18 := by decide +kernel
private theorem not_next1182_part03_ids19 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids19 := by decide +kernel
private theorem not_next1182_part03_ids20 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids20 := by decide +kernel
private theorem not_next1182_part03_ids21 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids21 := by decide +kernel
private theorem not_next1182_part03_ids22 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids22 := by decide +kernel
private theorem not_next1182_part03_ids23 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.ids23 := by decide +kernel
private theorem not_next1182_part03 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S03.newIDs := by
  rw [Paid16GeneralNext1182S03.new_mem]
  push_neg
  exact ⟨not_next1182_part03_ids16, not_next1182_part03_ids17,
    not_next1182_part03_ids18, not_next1182_part03_ids19,
    not_next1182_part03_ids20, not_next1182_part03_ids21,
    not_next1182_part03_ids22, not_next1182_part03_ids23⟩
private theorem not_next1182_part04_ids24 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids24 := by
  decide +kernel
private theorem not_next1182_part04_ids25 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids25 := by
  decide +kernel
private theorem not_next1182_part04_ids26 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids26 := by
  decide +kernel
private theorem not_next1182_part04_ids27 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids27 := by
  decide +kernel
private theorem not_next1182_part04_ids28 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids28 := by
  decide +kernel
private theorem not_next1182_part04_ids29 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids29 := by
  decide +kernel
private theorem not_next1182_part04_ids30 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids30 := by
  decide +kernel
private theorem not_next1182_part04_ids31 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.ids31 := by
  decide +kernel
private theorem not_next1182_part04 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S04.newIDs := by
  rw [Paid16GeneralNext1182S04.new_mem]
  push_neg
  exact ⟨not_next1182_part04_ids24, not_next1182_part04_ids25, not_next1182_part04_ids26, not_next1182_part04_ids27, not_next1182_part04_ids28, not_next1182_part04_ids29, not_next1182_part04_ids30, not_next1182_part04_ids31⟩
private theorem not_next1182_part05_ids32 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids32 := by
  decide +kernel
private theorem not_next1182_part05_ids33 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids33 := by
  decide +kernel
private theorem not_next1182_part05_ids34 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids34 := by
  decide +kernel
private theorem not_next1182_part05_ids35 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids35 := by
  decide +kernel
private theorem not_next1182_part05_ids36 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids36 := by
  decide +kernel
private theorem not_next1182_part05_ids37 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids37 := by
  decide +kernel
private theorem not_next1182_part05_ids38 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids38 := by
  decide +kernel
private theorem not_next1182_part05_ids39 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.ids39 := by
  decide +kernel
private theorem not_next1182_part05 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S05.newIDs := by
  rw [Paid16GeneralNext1182S05.new_mem]
  push_neg
  exact ⟨not_next1182_part05_ids32, not_next1182_part05_ids33, not_next1182_part05_ids34, not_next1182_part05_ids35, not_next1182_part05_ids36, not_next1182_part05_ids37, not_next1182_part05_ids38, not_next1182_part05_ids39⟩
private theorem not_next1182_part06_ids40 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids40 := by
  decide +kernel
private theorem not_next1182_part06_ids41 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids41 := by
  decide +kernel
private theorem not_next1182_part06_ids42 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids42 := by
  decide +kernel
private theorem not_next1182_part06_ids43 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids43 := by
  decide +kernel
private theorem not_next1182_part06_ids44 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids44 := by
  decide +kernel
private theorem not_next1182_part06_ids45 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids45 := by
  decide +kernel
private theorem not_next1182_part06_ids46 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids46 := by
  decide +kernel
private theorem not_next1182_part06_ids47 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.ids47 := by
  decide +kernel
private theorem not_next1182_part06 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S06.newIDs := by
  rw [Paid16GeneralNext1182S06.new_mem]
  push_neg
  exact ⟨not_next1182_part06_ids40, not_next1182_part06_ids41, not_next1182_part06_ids42, not_next1182_part06_ids43, not_next1182_part06_ids44, not_next1182_part06_ids45, not_next1182_part06_ids46, not_next1182_part06_ids47⟩
private theorem not_next1182_part07_ids48 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids48 := by
  decide +kernel
private theorem not_next1182_part07_ids49 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids49 := by
  decide +kernel
private theorem not_next1182_part07_ids50 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids50 := by
  decide +kernel
private theorem not_next1182_part07_ids51 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids51 := by
  decide +kernel
private theorem not_next1182_part07_ids52 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids52 := by
  decide +kernel
private theorem not_next1182_part07_ids53 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids53 := by
  decide +kernel
private theorem not_next1182_part07_ids54 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids54 := by
  decide +kernel
private theorem not_next1182_part07_ids55 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.ids55 := by
  decide +kernel
private theorem not_next1182_part07 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S07.newIDs := by
  rw [Paid16GeneralNext1182S07.new_mem]
  push_neg
  exact ⟨not_next1182_part07_ids48, not_next1182_part07_ids49, not_next1182_part07_ids50, not_next1182_part07_ids51, not_next1182_part07_ids52, not_next1182_part07_ids53, not_next1182_part07_ids54, not_next1182_part07_ids55⟩
private theorem not_next1182_part08 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182S08.newIDs := by
  decide +kernel
private theorem not_next1182 :
    (4244 : Fin 5011) ∉ Paid16GeneralNext1182.newIDs := by
  rw [Paid16GeneralNext1182.new_mem]
  push_neg
  exact ⟨not_next1182_part01, not_next1182_part02, not_next1182_part03,
    not_next1182_part04, not_next1182_part05, not_next1182_part06,
    not_next1182_part07, not_next1182_part08⟩

theorem not_paid_4244 : (4244 : Fin 5011) ∉ EnergyTerminalBatchB13.paidIDs := by
  intro h
  rw [EnergyTerminalBatchB13.paidIDs, Finset.mem_union] at h
  rcases h with h12 | h1182
  · rw [EnergyTerminalBatchB12.paidIDs, Finset.mem_union] at h12
    rcases h12 with h11 | h505
    · rw [EnergyTerminalBatchB11.paidIDs, Finset.mem_union] at h11
      rcases h11 with h10 | h210
      · have h10' : (4244 : Fin 5011) ∉ EnergyTerminalBatchB10.paidIDs := by
          decide +kernel
        exact h10' h10
      · have h210' : (4244 : Fin 5011) ∉ Paid16GeneralRemaining210.newIDs := by
          decide +kernel
        exact h210' h210
    · have hlt := EnergyTerminalBatchB13Next505Bounds.next505_lt (4244 : Fin 5011) h505
      omega
  · exact not_next1182 h1182

theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB13.paidIDs EnergyRefineN4244.newIDs := by
  rw [EnergyRefineN4244.newIDs, Finset.disjoint_left]
  intro a ha hb
  have ha' : a = 4244 := by simpa using hb
  subst a
  exact not_paid_4244 ha

theorem new_count : EnergyRefineN4244.newIDs.card = 1 := by
  simp [EnergyRefineN4244.newIDs]

theorem paid_count : paidIDs.card = 1998 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB13.paid_count, new_count]

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13.paid_terminal n hn
  · exact EnergyRefineN4244.new_terminal n hn

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_union.mp hn with hn | hn
  · exact EnergyTerminalBatchB13.paid_radius n hn y hy0 hy1 hc C Z r hf
  · exact EnergyRefineN4244.new_radius n hn y hy0 hy1 hc C Z r hf

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, (DBMSourceTree.data n).terminal = true →
    n ∉ Patch120SharpDispatch.sharpIDs → n ∉ paidIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

theorem remaining_of (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  intro n ht hs hp y hy0 hy1 hc C Z r hf
  by_cases hn : n ∈ EnergyRefineN4244.newIDs
  · exact (EnergyRefineN4244.new_radius n hn y hy0 hy1 hc C Z r hf).le
  · have hrest := h n ht hs (by
      intro hpn
      rcases Finset.mem_union.mp hpn with hpb | hpn
      · exact hp hpb
      · exact hn hpn)
    exact hrest y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13Refine4244
#check @N11Formalization.EnergyTerminalBatchB13Refine4244.paid_count
#check @N11Formalization.EnergyTerminalBatchB13Refine4244.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13Refine4244.remaining_of
#print axioms N11Formalization.EnergyTerminalBatchB13Refine4244.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13Refine4244.remaining_of
