import N11Formalization.EnergyTerminalBatchB12
import N11Formalization.Paid16GeneralNext1182
import N11Formalization.EnergyTerminalBatchB13Next505Bounds
import N11Formalization.EnergyTerminalBatchB13DescentBounds

/-! One thousand nine hundred ninety-seven actual energy terminals on the
SAME closed truechart: 815 from B12 plus the 1182 `rest1182` packets.
`RemainingTerminalRadius` is still explicit and UNPROVED, now over 389 ids. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB12.paidIDs ∪ Paid16GeneralNext1182.newIDs

private theorem b11_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB11.paidIDs) :
    n.val < 2565 ∨ n ∈ EnergyTerminalBatchB13DescentBounds.b09HighIDs :=
  EnergyTerminalBatchB13DescentBounds.b11_bound n hn

private theorem next505_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralNext505.newIDs) :
    n.val < 2565 := by
  exact N11Formalization.EnergyTerminalBatchB13Next505Bounds.next505_lt n hn

theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB12.paidIDs Paid16GeneralNext1182.newIDs := by
  rw [EnergyTerminalBatchB12.paidIDs, Finset.disjoint_union_left]
  constructor
  · rw [Finset.disjoint_left]
    intro a ha hb
    have hb' := b11_bound a ha
    have hge := Paid16GeneralNext1182.lower_bound a hb
    rcases hb' with hlt | hhigh
    · omega
    · exact EnergyTerminalBatchB13DescentBounds.high_not_next a hhigh hb
  · rw [Finset.disjoint_left]
    intro a ha hb
    have hlt := next505_lt a ha
    have hge := Paid16GeneralNext1182.lower_bound a hb
    omega

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
