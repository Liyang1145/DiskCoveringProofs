import N11Formalization.DSHTerminalBatchL0G1Zplus_562
import N11Formalization.DBMSourceTreeData

/-! Actual angular aggregation of terminal562's proved minorants. Rounded-down
nonnegative pair weights are explicit proposals; their field/oracle binding is
a separate obligation. No assumption about a numerical energy or LP optimum. -/
set_option autoImplicit false
namespace N11Formalization.Terminal562SimplexEnergy
open Finset FlashCosine
open DSHTerminalBatchL0G1Zplus562 (PA PB slopeQ interQ pair_minorant)
open FlashCosineLeaf284Bridge (iOf jOf)

def WN : Fin 36 → ℤ := ![2150718,111955,63409694,55521975,49876466,14423027,
  115989863,368091959,1250775,66497,61451,0,18445,24412,36331,29714,27452,0,
  8231,10894,12317,368976298,115971064,14487128,49980102,55563118,455854646,
  12688268,43766005,48653576,193788341,59698125,43670231,196534308,12833498,456614034]
def W (k : Fin 36) : ℚ := (WN k : ℚ)/10000000000
def cl : ℚ := ∑ k : Fin 36, W k * slopeQ k * ((iOf k).val - (jOf k).val : ℚ)
def f0 : ℚ := ∑ k : Fin 36,
  W k * (slopeQ k * ((iOf k).val - (jOf k).val : ℚ) * LQ + interQ k)
def g (q : Fin 9) : ℚ := ∑ k : Fin 36,
  if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val then W k * slopeQ k else 0

theorem W_nonneg : ∀ k : Fin 36, 0 ≤ W k := by decide +kernel
theorem pair_order : ∀ k : Fin 36, (iOf k).val < (jOf k).val := by decide +kernel
theorem cl_nonpos : cl ≤ 0 := by decide +kernel
theorem f0_lower : (14444 : ℚ)/100000 < f0 := by decide +kernel
theorem g_lower : ∀ q : Fin 9, -(1 : ℚ)/100000000 ≤ g q := by decide +kernel

noncomputable def affine (y : Fin 9 → ℝ) : ℝ := ∑ k : Fin 36,
  (W k : ℝ) * ((slopeQ k : ℝ)*zval y (iOf k) (jOf k)+(interQ k : ℝ))
noncomputable def energy (y : Fin 9 → ℝ) : ℝ := ∑ k : Fin 36,
  (W k : ℝ)*(1-Real.cos (zval y (iOf k) (jOf k)))

theorem affine_identity (y : Fin 9 → ℝ) :
    affine y = (f0 : ℝ)+(cl : ℝ)*(Lc-(LQ : ℝ))+
      Dc*(∑ q : Fin 9, (g q : ℝ)*y q) := by
  have he (k : Fin 36) :
      zval y (iOf k) (jOf k) =
      ((iOf k).val-(jOf k).val : ℝ)*Lc+
        Dc*(∑ q : Fin 9, if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val
          then y q else 0) := by
    rw [zval_eq, tval_sub y (Nat.le_of_lt (pair_order k))]
    rfl
  have hg : Dc*(∑ q : Fin 9, (g q : ℝ)*y q) =
      ∑ k : Fin 36, (W k : ℝ)*(slopeQ k : ℝ)*Dc*
        (∑ q : Fin 9, if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val
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

theorem affine_lower (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1) :
    (14444 : ℝ)/100000-1/100000000 < affine y := by
  have hg : -(1 : ℝ)/100000000 ≤ ∑ q : Fin 9,(g q : ℝ)*y q := by
    have h := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin 9))) =>
      mul_le_mul_of_nonneg_right (show -(1 : ℝ)/100000000 ≤ (g q : ℝ) from
        by exact_mod_cast g_lower q) (hy0 q))
    simpa [← Finset.mul_sum,hy1] using h
  have hc : 0 ≤ (cl : ℝ)*(Lc-(LQ : ℝ)) :=
    mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast cl_nonpos)
      (sub_nonpos.mpr L_mem.2)
  have hD0 : 0 ≤ Dc := le_trans (by exact_mod_cast Dq_pos.le) D_mem.1
  have hD1 : Dc ≤ 1 := D_mem.2.trans (by norm_num [DQ,Dq,LQ,RatInterval.piLo])
  have hf : (14444 : ℝ)/100000 < (f0 : ℝ) := by
    have h : ((14444/100000 : ℚ) : ℝ) < (f0 : ℝ) := Rat.cast_lt.mpr f0_lower
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  rw [affine_identity]
  nlinarith [mul_le_mul_of_nonneg_left hg hD0]

/-- Full36-pair energy inequality, consuming every previously proved pair minorant.
Cell-to-angular-bracket and real harmonic-field/oracle binding remain separate. -/
theorem energy_gt (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hz : ∀ k : Fin 36, zval y (iOf k) (jOf k) ∈ Set.Icc (PA k : ℝ) (PB k : ℝ)) :
    (1899919265599193545242591 / 5000000000000000000000000 : ℝ)^2 < energy y := by
  have hle : affine y ≤ energy y := Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_left (pair_minorant k _ (hz k))
      (by exact_mod_cast W_nonneg k))
  have hnum :
      (1899919265599193545242591 / 5000000000000000000000000 : ℝ)^2 <
        14444/100000-1/100000000 := by norm_num
  exact hnum.trans ((affine_lower y hy0 hy1).trans_le hle)

def db (i j : Fin 10) : ℤ := DBMSourceTree.node562.db i j
def slo (k : Fin 36) : ℚ :=
  max (-(db (jOf k).castSucc (iOf k).castSucc : ℚ)/4096) 0
def shi (k : Fin 36) : ℚ := (db (iOf k).castSucc (jOf k).castSucc : ℚ)/4096

theorem endpoint_binding : ∀ k : Fin 36,
    PA k ≤ ((iOf k).val-(jOf k).val : ℚ)*LQ+Dq*slo k ∧
    ((iOf k).val-(jOf k).val : ℚ)*Lq+DQ*shi k ≤ PB k := by decide +kernel

theorem angles_in_cell (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
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

theorem energy_gt_on_actual_terminal (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
      (FlashLeafSplit.tlift y)) :
    (1899919265599193545242591 / 5000000000000000000000000 : ℝ)^2 < energy y :=
  energy_gt y hy0 hy1 (angles_in_cell y hy0 hcell)

/-- Calibration to the existing threshold constant, not a new radius definition. -/
theorem threshold_identity :
    (1899919265599193545242591 / 5000000000000000000000000 : ℝ) =
      (FlashCosineLeaf284Bridge.T : ℝ) := by
  norm_num [FlashCosineLeaf284Bridge.T]

/-- Negative control: zero weights cannot be substituted into the strict energy consumer. -/
theorem zero_weights_rejected (y : Fin 9 → ℝ) :
    ¬ ((1899919265599193545242591 / 5000000000000000000000000 : ℝ)^2 <
      ∑ k : Fin 36, (0 : ℝ)*(1-Real.cos (zval y (iOf k) (jOf k)))) := by
  simp only [zero_mul,Finset.sum_const_zero]
  norm_num

end N11Formalization.Terminal562SimplexEnergy
#check @N11Formalization.Terminal562SimplexEnergy.energy_gt
#print axioms N11Formalization.Terminal562SimplexEnergy.energy_gt
#check @N11Formalization.Terminal562SimplexEnergy.energy_gt_on_actual_terminal
#print axioms N11Formalization.Terminal562SimplexEnergy.energy_gt_on_actual_terminal
#print axioms N11Formalization.Terminal562SimplexEnergy.zero_weights_rejected
