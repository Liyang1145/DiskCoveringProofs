import N11Formalization.DSHTerminalBatchL0G1Zplus_984
import N11Formalization.DBMSourceTreeData

/-! Actual node984 DBM->angular intervals for984's OWN36 minorants.
No562 interval/cell transfer; every endpoint-binding check must pass kernel. -/
set_option autoImplicit false
namespace N11Formalization.Terminal984Angles
open Finset FlashCosine
open FlashCosineLeaf284Bridge (iOf jOf)
open DSHTerminalBatchL0G1Zplus984 (PA PB)
set_option maxRecDepth 10000
theorem pair_order : ∀ k : Fin 36,(iOf k).val<(jOf k).val := by decide +kernel
def db (i j : Fin 10) : ℤ := DBMSourceTree.node984.db i j
def slo (k : Fin 36) : ℚ :=
  max (-(db (jOf k).castSucc (iOf k).castSucc : ℚ)/4096) 0
def shi (k : Fin 36) : ℚ := (db (iOf k).castSucc (jOf k).castSucc : ℚ)/4096

theorem endpoint_binding : ∀ k : Fin 36,
    PA k ≤ ((iOf k).val-(jOf k).val : ℚ)*LQ+Dq*slo k ∧
    ((iOf k).val-(jOf k).val : ℚ)*Lq+DQ*shi k ≤ PB k := by decide +kernel

theorem angles_in_cell (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
      (FlashLeafSplit.tlift y)) :
    ∀ k : Fin 36, zval y (iOf k) (jOf k) ∈ Set.Icc (PA k : ℝ) (PB k : ℝ) := by
  intro k
  have hu := hcell (iOf k).castSucc (jOf k).castSucc
  have hl := hcell (jOf k).castSucc (iOf k).castSucc
  simp only [← FlashCosineLeaf284Bridge.tval_eq_tlift] at hu hl
  change tval y (jOf k).castSucc-tval y (iOf k).castSucc ≤
    (db (iOf k).castSucc (jOf k).castSucc : ℝ)/4096 at hu
  change tval y (iOf k).castSucc-tval y (jOf k).castSucc ≤
    (db (jOf k).castSucc (iOf k).castSucc : ℝ)/4096 at hl
  have hsig0 : 0 ≤ tval y (jOf k).castSucc-tval y (iOf k).castSucc := by
    rw [tval_sub y (Nat.le_of_lt (pair_order k))]
    exact Finset.sum_nonneg (fun q _ => by split_ifs <;> first | exact hy0 q | exact le_rfl)
  have hsl : (slo k : ℝ) ≤ tval y (jOf k).castSucc-tval y (iOf k).castSucc := by
    simp only [slo,Rat.cast_max,Rat.cast_div,Rat.cast_neg,Rat.cast_intCast,
      Rat.cast_ofNat,Rat.cast_zero,max_le_iff]
    constructor
    · linarith [hl]
    · exact hsig0
  have hsh : tval y (jOf k).castSucc-tval y (iOf k).castSucc ≤ (shi k : ℝ) := by
    simpa only [shi,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using hu
  have h := cell_bound (pair_order k) (show (0 : ℚ) ≤ slo k from le_max_right _ _)
    L_mem.1 L_mem.2 D_mem.1 D_mem.2 hsl hsh
  rw [← zval_eq] at h
  have hlo : (PA k : ℝ) ≤
      (((iOf k).val-(jOf k).val : ℚ)*LQ+Dq*slo k : ℚ) := by
    exact_mod_cast (endpoint_binding k).1
  have hhi : (((iOf k).val-(jOf k).val : ℚ)*Lq+DQ*shi k : ℚ) ≤ (PB k : ℝ) := by
    exact_mod_cast (endpoint_binding k).2
  exact ⟨hlo.trans h.1,h.2.trans hhi⟩


end N11Formalization.Terminal984Angles
#check @N11Formalization.Terminal984Angles.endpoint_binding
#check @N11Formalization.Terminal984Angles.angles_in_cell
#print axioms N11Formalization.Terminal984Angles.angles_in_cell
