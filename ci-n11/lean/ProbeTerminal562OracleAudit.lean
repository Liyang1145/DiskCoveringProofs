import N11Formalization
open N11Formalization
#check @Terminal562Oracle.W_field10
#check @Terminal562Oracle.energy_le_oracle
#check @Terminal562Oracle.oracle_gt
#check @Terminal562Oracle.radius_gt
#check @Terminal562Oracle.sourceRadius_lt_feasible
#check @Terminal562Oracle.sourceRadius_lt_from_rows
#check @Terminal562Oracle.actual_node_is_terminal
#check @Terminal562Oracle.wrong_node_table_rejected
#print axioms Terminal562Oracle.oracle_gt
#print axioms Terminal562Oracle.sourceRadius_lt_from_rows
#print axioms Terminal562Oracle.wrong_node_table_rejected
#print SourceExactRoot.sourceRadius
#check SourceExactRoot.source_attainment
#check SourceExactRoot.main_of_lower_bound

namespace Terminal562CellCalibration
def q : Fin 9 → ℚ := ![0,0,0,5/16,1/16,0,1/16,1/8,7/16]
def tq (i : Fin 10) : ℚ := ∑ j : Fin 9, if j.val < i.val then q j else 0
theorem q_nonneg : ∀ j : Fin 9, 0 ≤ q j := by decide +kernel
theorem q_sum : ∑ j : Fin 9, q j = 1 := by decide +kernel
theorem q_cell : ∀ i j : Fin 10,
    tq j-tq i ≤ (DBMSourceTree.node562.db i j : ℚ)/4096 := by decide +kernel
theorem cell_nonempty :
    ∃ y : Fin 9 → ℝ, (∀ j, 0 ≤ y j) ∧ (∑ j,y j=1) ∧
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
        (FlashLeafSplit.tlift y) := by
  refine ⟨fun j => (q j : ℝ), ?_, ?_, ?_⟩
  · intro j
    change (0 : ℝ) ≤ (q j : ℝ)
    exact_mod_cast q_nonneg j
  · change (∑ j : Fin 9,(q j : ℝ)) = 1
    exact_mod_cast q_sum
  · intro i j
    simp only [← FlashCosineLeaf284Bridge.tval_eq_tlift]
    change (∑ k : Fin 9,if k.val < j.val then (q k : ℝ) else 0)-
      (∑ k : Fin 9,if k.val < i.val then (q k : ℝ) else 0) ≤
        (DBMSourceTree.node562.db i j : ℝ)/4096
    have h := (show ((tq j-tq i : ℚ) : ℝ) ≤
      (((DBMSourceTree.node562.db i j : ℚ)/4096 : ℚ) : ℝ) from Rat.cast_le.mpr (q_cell i j))
    simpa only [tq,Rat.cast_sub,Rat.cast_sum,apply_ite,Rat.cast_zero,
      Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using h
end Terminal562CellCalibration
#print axioms Terminal562CellCalibration.cell_nonempty
