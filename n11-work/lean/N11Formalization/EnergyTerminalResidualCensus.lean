import N11Formalization.EnergyTerminalResidualCensusC01
import N11Formalization.EnergyTerminalResidualCensusC02
import N11Formalization.EnergyTerminalResidualCensusC03
import N11Formalization.EnergyTerminalResidualCensusC04

/-! Assembly of the 389-element B13 residual census from four
source-index parts.  No single kernel decision covers more than 101 literals. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

private theorem chunk0_disjoint_chunk1 : Disjoint chunk0 chunk1 := by decide +kernel
private theorem chunk0_disjoint_chunk2 : Disjoint chunk0 chunk2 := by decide +kernel
private theorem chunk0_disjoint_chunk3 : Disjoint chunk0 chunk3 := by decide +kernel
private theorem chunk1_disjoint_chunk2 : Disjoint chunk1 chunk2 := by decide +kernel
private theorem chunk1_disjoint_chunk3 : Disjoint chunk1 chunk3 := by decide +kernel
private theorem chunk2_disjoint_chunk3 : Disjoint chunk2 chunk3 := by decide +kernel
private theorem chunk0_disjoint : Disjoint chunk0 (chunk1 ∪ (chunk2 ∪ chunk3)) := by
  rw [Finset.disjoint_union_right]
  exact ⟨chunk0_disjoint_chunk1, by
    rw [Finset.disjoint_union_right]
    exact ⟨chunk0_disjoint_chunk2, chunk0_disjoint_chunk3⟩⟩
private theorem chunk1_disjoint : Disjoint chunk1 (chunk2 ∪ chunk3) := by
  rw [Finset.disjoint_union_right]
  exact ⟨chunk1_disjoint_chunk2, chunk1_disjoint_chunk3⟩
private theorem chunk2_disjoint : Disjoint chunk2 chunk3 := chunk2_disjoint_chunk3
theorem residualIDs_card : residualIDs.card = 389 := by
  rw [residualIDs, Finset.card_union_of_disjoint chunk0_disjoint, chunk0_card]
  rw [Finset.card_union_of_disjoint chunk1_disjoint, chunk1_card]
  rw [Finset.card_union_of_disjoint chunk2_disjoint, chunk2_card]
  rw [chunk3_card]
  norm_num
theorem residualIDs_eq :
    residualIDs = EnergyTerminalBatchB13.residualIDs := by
  ext n
  have hcover : n.val < 100 ∨ (100 ≤ n.val ∧ n.val < 200) ∨ (200 ≤ n.val ∧ n.val < 300) ∨ (300 ≤ n.val ∧ n.val < 400) ∨ (400 ≤ n.val ∧ n.val < 500) ∨ (500 ≤ n.val ∧ n.val < 600) ∨ (600 ≤ n.val ∧ n.val < 700) ∨ (700 ≤ n.val ∧ n.val < 800) ∨ (800 ≤ n.val ∧ n.val < 900) ∨ (900 ≤ n.val ∧ n.val < 1000) ∨ (1000 ≤ n.val ∧ n.val < 1100) ∨ (1100 ≤ n.val ∧ n.val < 1200) ∨ (1200 ≤ n.val ∧ n.val < 1300) ∨ (1300 ≤ n.val ∧ n.val < 1400) ∨ (1400 ≤ n.val ∧ n.val < 1500) ∨ (1500 ≤ n.val ∧ n.val < 1600) ∨ (1600 ≤ n.val ∧ n.val < 1700) ∨ (1700 ≤ n.val ∧ n.val < 1800) ∨ (1800 ≤ n.val ∧ n.val < 1900) ∨ (1900 ≤ n.val ∧ n.val < 2000) ∨ (2000 ≤ n.val ∧ n.val < 2100) ∨ (2100 ≤ n.val ∧ n.val < 2200) ∨ (2200 ≤ n.val ∧ n.val < 2300) ∨ (2300 ≤ n.val ∧ n.val < 2400) ∨ (2400 ≤ n.val ∧ n.val < 2500) ∨ (2500 ≤ n.val ∧ n.val < 2600) ∨ (2600 ≤ n.val ∧ n.val < 2700) ∨ (2700 ≤ n.val ∧ n.val < 2800) ∨ (2800 ≤ n.val ∧ n.val < 2900) ∨ (2900 ≤ n.val ∧ n.val < 3000) ∨ (3000 ≤ n.val ∧ n.val < 3100) ∨ (3100 ≤ n.val ∧ n.val < 3200) ∨ (3200 ≤ n.val ∧ n.val < 3300) ∨ (3300 ≤ n.val ∧ n.val < 3400) ∨ (3400 ≤ n.val ∧ n.val < 3500) ∨ (3500 ≤ n.val ∧ n.val < 3600) ∨ (3600 ≤ n.val ∧ n.val < 3700) ∨ (3700 ≤ n.val ∧ n.val < 3800) ∨ (3800 ≤ n.val ∧ n.val < 3900) ∨ (3900 ≤ n.val ∧ n.val < 4000) ∨ (4000 ≤ n.val ∧ n.val < 4100) ∨ (4100 ≤ n.val ∧ n.val < 4200) ∨ (4200 ≤ n.val ∧ n.val < 4300) ∨ (4300 ≤ n.val ∧ n.val < 4400) ∨ (4400 ≤ n.val ∧ n.val < 4500) ∨ (4500 ≤ n.val ∧ n.val < 4600) ∨ (4600 ≤ n.val ∧ n.val < 4700) ∨ (4700 ≤ n.val ∧ n.val < 4800) ∨ (4800 ≤ n.val ∧ n.val < 4900) ∨ (4900 ≤ n.val ∧ n.val < 5000) ∨ 5000 ≤ n.val := by omega
  rcases hcover with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50
  · exact mem_iff_block00 n (Nat.zero_le _) h0
  · exact mem_iff_block01 n h1.1 h1.2
  · exact mem_iff_block02 n h2.1 h2.2
  · exact mem_iff_block03 n h3.1 h3.2
  · exact mem_iff_block04 n h4.1 h4.2
  · exact mem_iff_block05 n h5.1 h5.2
  · exact mem_iff_block06 n h6.1 h6.2
  · exact mem_iff_block07 n h7.1 h7.2
  · exact mem_iff_block08 n h8.1 h8.2
  · exact mem_iff_block09 n h9.1 h9.2
  · exact mem_iff_block10 n h10.1 h10.2
  · exact mem_iff_block11 n h11.1 h11.2
  · exact mem_iff_block12 n h12.1 h12.2
  · exact mem_iff_block13 n h13.1 h13.2
  · exact mem_iff_block14 n h14.1 h14.2
  · exact mem_iff_block15 n h15.1 h15.2
  · exact mem_iff_block16 n h16.1 h16.2
  · exact mem_iff_block17 n h17.1 h17.2
  · exact mem_iff_block18 n h18.1 h18.2
  · exact mem_iff_block19 n h19.1 h19.2
  · exact mem_iff_block20 n h20.1 h20.2
  · exact mem_iff_block21 n h21.1 h21.2
  · exact mem_iff_block22 n h22.1 h22.2
  · exact mem_iff_block23 n h23.1 h23.2
  · exact mem_iff_block24 n h24.1 h24.2
  · exact mem_iff_block25 n h25.1 h25.2
  · exact mem_iff_block26 n h26.1 h26.2
  · exact mem_iff_block27 n h27.1 h27.2
  · exact mem_iff_block28 n h28.1 h28.2
  · exact mem_iff_block29 n h29.1 h29.2
  · exact mem_iff_block30 n h30.1 h30.2
  · exact mem_iff_block31 n h31.1 h31.2
  · exact mem_iff_block32 n h32.1 h32.2
  · exact mem_iff_block33 n h33.1 h33.2
  · exact mem_iff_block34 n h34.1 h34.2
  · exact mem_iff_block35 n h35.1 h35.2
  · exact mem_iff_block36 n h36.1 h36.2
  · exact mem_iff_block37 n h37.1 h37.2
  · exact mem_iff_block38 n h38.1 h38.2
  · exact mem_iff_block39 n h39.1 h39.2
  · exact mem_iff_block40 n h40.1 h40.2
  · exact mem_iff_block41 n h41.1 h41.2
  · exact mem_iff_block42 n h42.1 h42.2
  · exact mem_iff_block43 n h43.1 h43.2
  · exact mem_iff_block44 n h44.1 h44.2
  · exact mem_iff_block45 n h45.1 h45.2
  · exact mem_iff_block46 n h46.1 h46.2
  · exact mem_iff_block47 n h47.1 h47.2
  · exact mem_iff_block48 n h48.1 h48.2
  · exact mem_iff_block49 n h49.1 h49.2
  · exact mem_iff_block50 n h50 n.isLt

theorem b13_residualIDs_card :
    EnergyTerminalBatchB13.residualIDs.card = 389 := by
  rw [← residualIDs_eq, residualIDs_card]

theorem residualIDs_sound :
    ∀ n ∈ residualIDs, (DBMSourceTree.data n).terminal = true ∧
      n ∉ Patch120SharpDispatch.sharpIDs ∧
      n ∉ EnergyTerminalBatchB13.paidIDs := by
  intro n hn
  rw [residualIDs_eq] at hn
  exact (EnergyTerminalBatchB13.mem_residualIDs_iff n).mp hn

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, n ∈ residualIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

theorem remaining_iff_b13 :
    RemainingTerminalRadius ↔ EnergyTerminalBatchB13.RemainingTerminalRadius := by
  rw [EnergyTerminalBatchB13.remaining_iff]
  constructor
  · intro h n hn
    rw [← residualIDs_eq] at hn
    exact h n hn
  · intro h n hn
    rw [residualIDs_eq] at hn
    exact h n hn
end
end N11Formalization.EnergyTerminalResidualCensus
#check @N11Formalization.EnergyTerminalResidualCensus.residualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensus.residualIDs_eq
#check @N11Formalization.EnergyTerminalResidualCensus.b13_residualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensus.remaining_iff_b13
#print axioms N11Formalization.EnergyTerminalResidualCensus.residualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensus.residualIDs_eq
#print axioms N11Formalization.EnergyTerminalResidualCensus.b13_residualIDs_card
