import N11Formalization.DBMMinorantDual

/-! Shared actual DBM4096 -> 36 angular minorant intervals.
No transfer of a different node's cell. Numeric endpoints explicit until paid. -/
set_option autoImplicit false
namespace N11Formalization.DBMAngleProvider
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.FlashCosineLeaf284Bridge (iOf jOf)
noncomputable section

def slo (n : Fin 5011) (k : Fin 36) : ℚ :=
  max (-DBMMinorantDual.db n (jOf k).castSucc (iOf k).castSucc) 0
def shi (n : Fin 5011) (k : Fin 36) : ℚ :=
  DBMMinorantDual.db n (iOf k).castSucc (jOf k).castSucc

theorem angles_of_endpoints (n : Fin 5011) (A B : Fin 36 → ℚ)
    (he : ∀ k,A k≤((iOf k).val-(jOf k).val : ℚ)*LQ+Dq*slo n k ∧
      ((iOf k).val-(jOf k).val : ℚ)*Lq+DQ*shi n k≤B k)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) :
    ∀ k : Fin 36,zval y (iOf k) (jOf k)∈Set.Icc (A k : ℝ) (B k : ℝ) := by
  intro k
  have hu := hc (iOf k).castSucc (jOf k).castSucc
  have hl := hc (jOf k).castSucc (iOf k).castSucc
  simp only [← FlashCosineLeaf284Bridge.tval_eq_tlift] at hu hl
  have hsig0 : 0≤tval y (jOf k).castSucc-tval y (iOf k).castSucc := by
    rw [tval_sub y (Nat.le_of_lt (Terminal562SimplexEnergy.pair_order k))]
    exact Finset.sum_nonneg (fun q _ => by split_ifs <;> first | exact hy0 q | exact le_rfl)
  have hsl : (slo n k : ℝ)≤tval y (jOf k).castSucc-tval y (iOf k).castSucc := by
    simp only [slo,DBMMinorantDual.db,Rat.cast_max,Rat.cast_neg,Rat.cast_div,
      Rat.cast_intCast,Rat.cast_ofNat,Rat.cast_zero,max_le_iff]
    constructor
    · norm_num only [DBMTreeKernel.matrix,Int.cast_ofNat] at hl
      linarith
    · exact hsig0
  have hsh : tval y (jOf k).castSucc-tval y (iOf k).castSucc≤(shi n k : ℝ) := by
    simpa only [shi,DBMMinorantDual.db,DBMTreeKernel.matrix,Rat.cast_div,
      Rat.cast_intCast,Rat.cast_ofNat,Int.cast_ofNat] using hu
  have h := cell_bound (Terminal562SimplexEnergy.pair_order k)
    (show (0 : ℚ) ≤ slo n k from le_max_right _ _)
    L_mem.1 L_mem.2 D_mem.1 D_mem.2 hsl hsh
  rw [← zval_eq] at h
  have hlo : (A k : ℝ)≤
      (((iOf k).val-(jOf k).val : ℚ)*LQ+Dq*slo n k : ℚ) := by
    exact_mod_cast (he k).1
  have hhi : (((iOf k).val-(jOf k).val : ℚ)*Lq+DQ*shi n k : ℚ)≤(B k : ℝ) := by
    exact_mod_cast (he k).2
  exact ⟨hlo.trans h.1,h.2.trans hhi⟩

end
end N11Formalization.DBMAngleProvider
#check @N11Formalization.DBMAngleProvider.angles_of_endpoints
#print axioms N11Formalization.DBMAngleProvider.angles_of_endpoints
