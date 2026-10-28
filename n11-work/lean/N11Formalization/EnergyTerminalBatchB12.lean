import N11Formalization.EnergyTerminalBatchB11
import N11Formalization.Paid16GeneralNext505

/-! Eight hundred fifteen actual energy terminals on the SAME closed truechart:
the 310 previously paid plus the 505 `next512` HOST packets.
`RemainingTerminalRadius` is still explicit and UNPROVED, but it now quantifies
over 1571 terminals instead of 2076. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB12
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB11.paidIDs ∪ Paid16GeneralNext505.newIDs
theorem paid_count : paidIDs.card = 815 := by
  rw [paidIDs, Finset.card_union_of_disjoint Paid16GeneralNext505.disjoint_paid,
    EnergyTerminalBatchB11.paid_count, Paid16GeneralNext505.new_count]
theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext505.newIDs :=
  Paid16GeneralNext505.disjoint_paid
theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by
  rw [paidIDs]
  exact Finset.disjoint_union_left.mpr
    ⟨EnergyTerminalBatchB11.paid_not_sharp, Paid16GeneralNext505.disjoint_sharp⟩
theorem paid_terminal (n : Fin 5011) (hn : n∈paidIDs) :
    (DBMSourceTree.data n).terminal=true := by
  have h : n∈EnergyTerminalBatchB11.paidIDs ∨ n∈Paid16GeneralNext505.newIDs := by
    simpa only [paidIDs,Finset.mem_union] using hn
  rcases h with h | h
  · exact EnergyTerminalBatchB11.paid_terminal n h
  · exact Paid16GeneralNext505.new_terminal n h
theorem paid_radius (n : Fin 5011) (hn : n∈paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius < r := by
  have h : n∈EnergyTerminalBatchB11.paidIDs ∨ n∈Paid16GeneralNext505.newIDs := by
    simpa only [paidIDs,Finset.mem_union] using hn
  rcases h with h | h
  · exact EnergyTerminalBatchB11.paid_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext505.new_radius n h y hy0 hy1 hc C Z r hf

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011,(DBMSourceTree.data n).terminal=true →
    n∉Patch120SharpDispatch.sharpIDs → n∉paidIDs →
    ∀ (y : Fin 9 → ℝ),(∀ q,0 ≤ y q) → (∑ q,y q=1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r
theorem chart_radius_of_remaining (hremaining : RemainingTerminalRadius)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius ≤ r := by
  obtain ⟨n,ht,hc⟩ := DBMTreeChartConsumer.chart9_terminal_cover y hy0 hy1
  by_cases hs : n∈Patch120SharpDispatch.sharpIDs
  · exact Patch120SharpDispatch.sharp_radius n hs y hc C Z r hf
  · by_cases he : n∈paidIDs
    · exact (paid_radius n he y hy0 hy1 hc C Z r hf).le
    · exact hremaining n ht hs he y hy0 hy1 hc C Z r hf

/-- Credit transfer: a B12 residual pays the B11 residual. -/
theorem remaining_of_b12 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB11.RemainingTerminalRadius := by
  intro n ht hs he y hy0 hy1 hc C Z r hf
  by_cases hp : n∈paidIDs
  · exact (paid_radius n hp y hy0 hy1 hc C Z r hf).le
  · exact h n ht hs hp y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB12
#check @N11Formalization.EnergyTerminalBatchB12.paid_count
#check @N11Formalization.EnergyTerminalBatchB12.paid_radius
#check @N11Formalization.EnergyTerminalBatchB12.chart_radius_of_remaining
#check @N11Formalization.EnergyTerminalBatchB12.remaining_of_b12
#print axioms N11Formalization.EnergyTerminalBatchB12.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB12.remaining_of_b12
