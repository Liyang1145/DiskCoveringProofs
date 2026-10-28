import N11Formalization.Terminal562SimplexEnergy
import N11Formalization.Leaf4348Fields7
import N11Formalization.SourceExactRoot

/-! Whole terminal562 consumer using the already-certified field10 (slot0 of
Leaf4348Fields7). Every weight comparison is kernel-checked, and the real
canonical51 harmonic/oracle consumer is actually applied. No stored energy
number, supplied field identity, or LP optimizer is assumed. -/
set_option autoImplicit false
namespace N11Formalization.Terminal562Oracle
open Finset FlashCosine
open DSHTerminalBatchL0G1Zplus562 (PA PB slopeQ interQ pair_minorant)
open FlashCosineLeaf284Bridge (iOf jOf)

def WN : Fin 36 → ℤ := ![9,2,63522614,55618359,50005637,14446141,
  116271410,369013395,8,2,1,0,0,0,1,9,1,0,0,0,1,369013403,116271406,
  14446141,50005637,55618358,457035222,12648578,43783330,48697647,
  194290215,59852732,43783328,194290229,12648577,457035225]
def W (k : Fin 36) : ℚ := (WN k : ℚ)/10000000000
def cl : ℚ := ∑ k : Fin 36, W k*slopeQ k*((iOf k).val-(jOf k).val : ℚ)
def f0 : ℚ := ∑ k : Fin 36,
  W k*(slopeQ k*((iOf k).val-(jOf k).val : ℚ)*LQ+interQ k)
def g (q : Fin 9) : ℚ := ∑ k : Fin 36,
  if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val then W k*slopeQ k else 0

theorem W_nonneg : ∀ k : Fin 36, 0 ≤ W k := by decide +kernel
theorem cl_nonpos : cl ≤ 0 := by decide +kernel
theorem f0_lower : (14442 : ℚ)/100000 < f0 := by decide +kernel
theorem g_nonneg : ∀ q : Fin 9, 0 ≤ g q := by decide +kernel

/-- Comparisons against the actual accepted field10 rational Gram weights,
not against an external list or the previous unbound mixture proposal. -/
theorem W_field10_rat : ∀ k : Fin 36,
    W k ≤ 2*((Leaf4348Fields7.wNum 0 k : ℚ)/(Leaf4348Fields7.wDen 0 k : ℚ)) := by
  decide +kernel

theorem W_field10 (k : Fin 36) :
    (W k : ℝ) ≤ 2*Leaf4348Fields7.weight 0 k := by
  have h : (W k : ℝ) ≤
      ((2*((Leaf4348Fields7.wNum 0 k : ℚ)/(Leaf4348Fields7.wDen 0 k : ℚ)) : ℚ) : ℝ) :=
    Rat.cast_le.mpr (W_field10_rat k)
  simpa only [Leaf4348Fields7.weight,Rat.cast_mul,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_intCast] using h

noncomputable def affine (y : Fin 9 → ℝ) : ℝ := ∑ k : Fin 36,
  (W k : ℝ)*((slopeQ k : ℝ)*zval y (iOf k) (jOf k)+(interQ k : ℝ))
noncomputable def energy (y : Fin 9 → ℝ) : ℝ := ∑ k : Fin 36,
  (W k : ℝ)*(1-Real.cos (zval y (iOf k) (jOf k)))

theorem affine_identity (y : Fin 9 → ℝ) :
    affine y = (f0 : ℝ)+(cl : ℝ)*(Lc-(LQ : ℝ))+
      Dc*(∑ q : Fin 9,(g q : ℝ)*y q) := by
  have he (k : Fin 36) :
      zval y (iOf k) (jOf k) =
      ((iOf k).val-(jOf k).val : ℝ)*Lc+
        Dc*(∑ q : Fin 9,if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val
          then y q else 0) := by
    rw [zval_eq,tval_sub y (Nat.le_of_lt (Terminal562SimplexEnergy.pair_order k))]
    rfl
  have hg : Dc*(∑ q : Fin 9,(g q : ℝ)*y q) =
      ∑ k : Fin 36,(W k : ℝ)*(slopeQ k : ℝ)*Dc*
        (∑ q : Fin 9,if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val
          then y q else 0) := by
    unfold g
    push_cast
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : (iOf k).val ≤ q.val ∧ q.val < (jOf k).val
    · simp only [if_pos h,Rat.cast_mul]
      ring
    · simp only [if_neg h,Rat.cast_zero,mul_zero,zero_mul]
  rw [hg]
  unfold affine f0 cl
  push_cast
  simp_rw [he]
  simp only [Finset.sum_mul]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem affine_lower (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) :
    (14442 : ℝ)/100000 < affine y := by
  have hg : 0 ≤ ∑ q : Fin 9,(g q : ℝ)*y q :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (by exact_mod_cast g_nonneg q) (hy0 q))
  have hc : 0 ≤ (cl : ℝ)*(Lc-(LQ : ℝ)) :=
    mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast cl_nonpos)
      (sub_nonpos.mpr L_mem.2)
  have hD0 : 0 ≤ Dc := le_trans (by exact_mod_cast Dq_pos.le) D_mem.1
  have hf : (14442 : ℝ)/100000 < (f0 : ℝ) := by
    have h : ((14442/100000 : ℚ) : ℝ) < (f0 : ℝ) := Rat.cast_lt.mpr f0_lower
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  rw [affine_identity]
  linarith [mul_nonneg hD0 hg]

theorem energy_gt_on_cell (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 < energy y := by
  have hz := Terminal562SimplexEnergy.angles_in_cell y hy0 hcell
  have hle : affine y ≤ energy y := Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_left (pair_minorant k _ (hz k))
      (by exact_mod_cast W_nonneg k))
  have ht : (FlashCosineLeaf284Bridge.T : ℝ)^2 < (14442 : ℝ)/100000 := by
    norm_num [FlashCosineLeaf284Bridge.T]
  exact ht.trans ((affine_lower y hy0).trans_le hle)

/-- Actual field10 is normalized, balanced and harmonic by its already-paid
kernel certificates. Its canonical51 oracle consumer discharges the final
energy semantic inequality for all angles. -/
theorem energy_le_oracle (y : Fin 9 → ℝ) :
    energy y ≤ ResumeNetwork.V2 (fun j => circleMap (theta y j)) := by
  have hle : energy y ≤ Leaf4348Fields7.fieldEnergy 0 (theta y) := by
    unfold energy Leaf4348Fields7.fieldEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have hc : 0 ≤ 1-Real.cos (zval y (iOf k) (jOf k)) := by
      linarith [Real.cos_le_one (zval y (iOf k) (jOf k))]
    have h := mul_le_mul_of_nonneg_right (W_field10 k) hc
    simpa only [zval,mul_assoc] using h
  exact hle.trans (Leaf4348Fields7.source_energy_le_oracle 0 (theta y))

theorem oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      ResumeNetwork.V2 (fun j => circleMap (theta y j)) :=
  (energy_gt_on_cell y hy0 hcell).trans_le (energy_le_oracle y)

theorem radius_gt (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
      (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (fun j => circleMap (theta y j)) C Z r) :
    (FlashCosineLeaf284Bridge.T : ℝ) < r := by
  have hlo := oracle_gt y hy0 hcell
  have hhi := ResumeNetwork.oracle_le_feasible hf
  have ht : (0 : ℝ) ≤ (FlashCosineLeaf284Bridge.T : ℝ) := by
    norm_num [FlashCosineLeaf284Bridge.T]
  have hr := hf.1
  nlinarith

theorem sourceRadius_lt_T :
    SourceExactRoot.sourceRadius < (FlashCosineLeaf284Bridge.T : ℝ) := by
  have he : C921Sem.threshR = (FlashCosineLeaf284Bridge.T : ℝ) := rfl
  rw [← he]
  exact SourceExactRoot.sourceRadius_lt_threshold

theorem sourceRadius_lt_feasible (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
      (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (fun j => circleMap (theta y j)) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  sourceRadius_lt_T.trans (radius_gt y hy0 hcell C Z r hf)

/-- Application to all18 boundary and all33 face rows. None of the six
slack primal rows is discarded. This is a genuine geometry-row consumer,
not a theorem about arbitrary Covers producing these rows. -/
theorem sourceRadius_lt_from_rows (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
      (FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ) (hr : 0 ≤ r)
    (hb : ∀ i : Fin 9, ∀ side : Fin 2,
      dist (C ⟨i.val,by omega⟩) (circleMap (theta y (ResumeNetwork.anchorIndex i side))) ≤ r)
    (hfaces : ∀ f : Fin 11, ∀ v : Fin 3,
      dist (C (ResumeNetwork.face f v)) (Z f) ≤ r) :
    SourceExactRoot.sourceRadius < r := by
  have hlo := oracle_gt y hy0 hcell
  have hhi := ResumeNetwork.oracle_le_of_geometric_witnesses
    (U := fun j => circleMap (theta y j)) (C := C) (Z := Z) (r := r) hr hb hfaces
  have ht : (0 : ℝ) ≤ (FlashCosineLeaf284Bridge.T : ℝ) := by
    norm_num [FlashCosineLeaf284Bridge.T]
  have hT : (FlashCosineLeaf284Bridge.T : ℝ) < r := by nlinarith
  exact sourceRadius_lt_T.trans hT

theorem actual_node_is_terminal : (DBMSourceTree.data (562 : Fin 5011)).terminal = true := by
  decide +kernel

theorem wrong_node_table_rejected :
    (DBMSourceTree.data (562 : Fin 5011)).db ≠ (DBMSourceTree.data (563 : Fin 5011)).db := by
  decide +kernel

end N11Formalization.Terminal562Oracle
#check @N11Formalization.Terminal562Oracle.oracle_gt
#check @N11Formalization.Terminal562Oracle.radius_gt
#print axioms N11Formalization.Terminal562Oracle.energy_le_oracle
#print axioms N11Formalization.Terminal562Oracle.oracle_gt
#print axioms N11Formalization.Terminal562Oracle.radius_gt
#check @N11Formalization.Terminal562Oracle.sourceRadius_lt_from_rows
#print axioms N11Formalization.Terminal562Oracle.sourceRadius_lt_from_rows
#print axioms N11Formalization.Terminal562Oracle.wrong_node_table_rejected
