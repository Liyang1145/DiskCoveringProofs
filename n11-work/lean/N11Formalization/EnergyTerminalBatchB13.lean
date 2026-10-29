import N11Formalization.EnergyTerminalBatchB12
import N11Formalization.Paid16GeneralNext1182

/-! One thousand nine hundred ninety-seven actual energy terminals on the
SAME closed truechart: 815 from B12 plus the 1182 `rest1182` packets.
`RemainingTerminalRadius` is still explicit and UNPROVED, now over 389 ids. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB12.paidIDs ∪ Paid16GeneralNext1182.newIDs

private theorem of_all_lt {s : Finset (Fin 5011)}
    (h : (s.all fun n => n.val < 2565) = true) :
    ∀ n, n ∈ s → n.val < 2565 := by
  intro n hn
  exact (Finset.all_eq_true.mp h) n hn

private theorem of_all_ge {s : Finset (Fin 5011)}
    (h : (s.all fun n => 2565 ≤ n.val) = true) :
    ∀ n, n ∈ s → 2565 ≤ n.val := by
  intro n hn
  exact (Finset.all_eq_true.mp h) n hn

private theorem next505_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralNext505.newIDs) :
    n.val < 2565 := by
  rcases (Paid16GeneralNext505.new_mem n).mp hn with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids00) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids01) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids02) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids03) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids04) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids05) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids06) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids07) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids08) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids09) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids10) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids11) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids12) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids13) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids14) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids15) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids16) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids17) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids18) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids19) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids20) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids21) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids22) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids23) (by decide +kernel)) n h
  · exact (of_all_lt (s := Paid16GeneralNext505.ids24) (by decide +kernel)) n h

private theorem s01_ge : ∀ n, n ∈ Paid16GeneralNext1182S01.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S01.newIDs) (by decide +kernel)
private theorem s02_ge : ∀ n, n ∈ Paid16GeneralNext1182S02.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S02.newIDs) (by decide +kernel)
private theorem s03_ge : ∀ n, n ∈ Paid16GeneralNext1182S03.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S03.newIDs) (by decide +kernel)
private theorem s04_ge : ∀ n, n ∈ Paid16GeneralNext1182S04.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S04.newIDs) (by decide +kernel)
private theorem s05_ge : ∀ n, n ∈ Paid16GeneralNext1182S05.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S05.newIDs) (by decide +kernel)
private theorem s06_ge : ∀ n, n ∈ Paid16GeneralNext1182S06.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S06.newIDs) (by decide +kernel)
private theorem s07_ge : ∀ n, n ∈ Paid16GeneralNext1182S07.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S07.newIDs) (by decide +kernel)
private theorem s08_ge : ∀ n, n ∈ Paid16GeneralNext1182S08.newIDs → 2565 ≤ n.val :=
  of_all_ge (s := Paid16GeneralNext1182S08.newIDs) (by decide +kernel)

private theorem b11_lt (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB11.paidIDs) :
    n.val < 1160 :=
  of_all_lt (s := EnergyTerminalBatchB11.paidIDs) (by decide +kernel) n hn

private theorem b11_disjoint_s01 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S01.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s01_ge n hs
  omega

private theorem b11_disjoint_s02 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S02.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s02_ge n hs
  omega

private theorem b11_disjoint_s03 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S03.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s03_ge n hs
  omega

private theorem b11_disjoint_s04 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S04.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s04_ge n hs
  omega

private theorem b11_disjoint_s05 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s05_ge n hs
  omega

private theorem b11_disjoint_s06 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s06_ge n hs
  omega

private theorem b11_disjoint_s07 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s07_ge n hs
  omega

private theorem b11_disjoint_s08 :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hb hs
  have hlt := b11_lt n hb
  have hge := s08_ge n hs
  omega

theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB12.paidIDs Paid16GeneralNext1182.newIDs := by
  rw [EnergyTerminalBatchB12.paidIDs, Finset.disjoint_union_left]
  constructor
  · rw [Finset.disjoint_left]
    intro a ha hb
    rcases (Paid16GeneralNext1182.new_mem a).mp hb with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · exact (Finset.disjoint_left.mp b11_disjoint_s01) (a := a) ha h1
    · exact (Finset.disjoint_left.mp b11_disjoint_s02) (a := a) ha h2
    · exact (Finset.disjoint_left.mp b11_disjoint_s03) (a := a) ha h3
    · exact (Finset.disjoint_left.mp b11_disjoint_s04) (a := a) ha h4
    · exact (Finset.disjoint_left.mp b11_disjoint_s05) (a := a) ha h5
    · exact (Finset.disjoint_left.mp b11_disjoint_s06) (a := a) ha h6
    · exact (Finset.disjoint_left.mp b11_disjoint_s07) (a := a) ha h7
    · exact (Finset.disjoint_left.mp b11_disjoint_s08) (a := a) ha h8
  · rw [Finset.disjoint_left]
    intro a ha hb
    have hlt := next505_lt a ha
    rcases (Paid16GeneralNext1182.new_mem a).mp hb with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    · have hge := s01_ge a h1; omega
    · have hge := s02_ge a h2; omega
    · have hge := s03_ge a h3; omega
    · have hge := s04_ge a h4; omega
    · have hge := s05_ge a h5; omega
    · have hge := s06_ge a h6; omega
    · have hge := s07_ge a h7; omega
    · have hge := s08_ge a h8; omega

theorem paid_count : paidIDs.card = 1997 := by
  rw [paidIDs, Finset.card_union_of_disjoint new_disjoint_old,
    EnergyTerminalBatchB12.paid_count, Paid16GeneralNext1182.new_count]

theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by
  rw [paidIDs]
  exact Finset.disjoint_union_left.mpr
    ⟨EnergyTerminalBatchB12.paid_not_sharp, Paid16GeneralNext1182.disjoint_sharp⟩

theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  have h : n ∈ EnergyTerminalBatchB12.paidIDs ∨ n ∈ Paid16GeneralNext1182.newIDs := by
    simpa only [paidIDs, Finset.mem_union] using hn
  rcases h with h | h
  · exact EnergyTerminalBatchB12.paid_terminal n h
  · exact Paid16GeneralNext1182.new_terminal n h

theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius < r := by
  have h : n ∈ EnergyTerminalBatchB12.paidIDs ∨ n ∈ Paid16GeneralNext1182.newIDs := by
    simpa only [paidIDs, Finset.mem_union] using hn
  rcases h with h | h
  · exact EnergyTerminalBatchB12.paid_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182.new_radius n h y hy0 hy1 hc C Z r hf

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, (DBMSourceTree.data n).terminal = true →
    n ∉ Patch120SharpDispatch.sharpIDs → n ∉ paidIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r

/-- The actual terminal ids not already paid by B13.  This is the census set
on which `RemainingTerminalRadius` is posed (389 elements by the rest1182
manifest's total-terminal count; that cardinality is not proved here). -/
def residualIDs : Finset (Fin 5011) :=
  (Finset.univ.filter fun n => (DBMSourceTree.data n).terminal = true).filter
    fun n => n ∉ Patch120SharpDispatch.sharpIDs ∧ n ∉ paidIDs

theorem mem_residualIDs_iff (n : Fin 5011) :
    n ∈ residualIDs ↔ (DBMSourceTree.data n).terminal = true ∧
      n ∉ Patch120SharpDispatch.sharpIDs ∧ n ∉ paidIDs := by
  simp only [residualIDs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem remaining_iff :
    RemainingTerminalRadius ↔ ∀ n, n ∈ residualIDs →
      ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
        FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
          (FlashLeafSplit.tlift y) →
        ∀ (C Z : Fin 11 → Point) (r : ℝ),
          Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r := by
  constructor
  · intro h n hn
    obtain ⟨ht, hs, hp⟩ := (mem_residualIDs_iff n).mp hn
    exact h n ht hs hp
  · intro h n ht hs hp
    exact h n ((mem_residualIDs_iff n).mpr ⟨ht, hs, hp⟩)

theorem chart_radius_of_remaining (hremaining : RemainingTerminalRadius)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius ≤ r := by
  obtain ⟨n, ht, hc⟩ := DBMTreeChartConsumer.chart9_terminal_cover y hy0 hy1
  by_cases hs : n ∈ Patch120SharpDispatch.sharpIDs
  · exact Patch120SharpDispatch.sharp_radius n hs y hc C Z r hf
  · by_cases he : n ∈ paidIDs
    · exact (paid_radius n he y hy0 hy1 hc C Z r hf).le
    · exact hremaining n ht hs he y hy0 hy1 hc C Z r hf

/-- Credit transfer: a B13 residual pays the B12 residual. -/
theorem remaining_of_b13 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB12.RemainingTerminalRadius := by
  intro n ht hs he y hy0 hy1 hc C Z r hf
  by_cases hp : n ∈ paidIDs
  · exact (paid_radius n hp y hy0 hy1 hc C Z r hf).le
  · apply h n ht hs hp y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB13
#check @N11Formalization.EnergyTerminalBatchB13.paid_count
#check @N11Formalization.EnergyTerminalBatchB13.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13.chart_radius_of_remaining
#check @N11Formalization.EnergyTerminalBatchB13.remaining_of_b13
#print axioms N11Formalization.EnergyTerminalBatchB13.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13.remaining_of_b13
