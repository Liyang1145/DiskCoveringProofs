import N11Formalization.EnergyTerminalBatchB06
import N11Formalization.Terminal4179Consumer
import N11Formalization.Terminal4265Consumer

/-! Thirty-five actual energy-terminal dispatch, once dependencies are paid.
RemainingTerminalRadius and arbitrary Covers reduction stay explicit. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB07
open SourceChartIsometry ResumeNetwork
noncomputable section
def paidIDs : Finset (Fin 5011) :=
  insert 4265 (insert 4179 EnergyTerminalBatchB06.paidIDs)
theorem new4179_not_old : (4179 : Fin 5011) ∉ EnergyTerminalBatchB06.paidIDs := by
  decide +kernel
theorem new4265_not_old : (4265 : Fin 5011) ∉ EnergyTerminalBatchB06.paidIDs := by
  decide +kernel
theorem paid_count : paidIDs.card = 35 := by decide +kernel
theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by
  decide +kernel
theorem paid_terminal (n : Fin 5011) (hn : n ∈ paidIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_insert.mp hn with rfl | hn
  · exact Terminal4265Packet.terminal
  · rcases Finset.mem_insert.mp hn with rfl | ho
    · exact Terminal4179Packet.terminal
    · exact EnergyTerminalBatchB06.paid_terminal n ho
theorem paid_radius (n : Fin 5011) (hn : n ∈ paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius < r := by
  rcases Finset.mem_insert.mp hn with rfl | hn
  · exact Terminal4265Consumer.common_chart_radius y hy0 hy1 hc C Z r hf
  · rcases Finset.mem_insert.mp hn with rfl | ho
    · exact Terminal4179Consumer.common_chart_radius y hy0 hy1 hc C Z r hf
    · exact EnergyTerminalBatchB06.paid_radius n ho y hy0 hy1 hc C Z r hf
def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, (DBMSourceTree.data n).terminal = true →
    n ∉ Patch120SharpDispatch.sharpIDs → n ∉ paidIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r
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
end
end N11Formalization.EnergyTerminalBatchB07
#check @N11Formalization.EnergyTerminalBatchB07.paid_count
#check @N11Formalization.EnergyTerminalBatchB07.paid_radius
#check @N11Formalization.EnergyTerminalBatchB07.chart_radius_of_remaining
#print axioms N11Formalization.EnergyTerminalBatchB07.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB07.chart_radius_of_remaining
