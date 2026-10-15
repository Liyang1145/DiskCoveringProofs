import N11Formalization.Terminal984Angles
import N11Formalization.EnergyCommonChart

/-! Real node984 ownminorant->pairenergy->true field10->V2->SAMEradius.
The weight proof is accepted for ALL angles, not a562 cell proof. No mixture/
membership/optimizer/energy number premise; simplex/cell/51Feasible explicit. -/
set_option autoImplicit false
namespace N11Formalization.Terminal984Oracle
open Finset FlashCosine
open FlashCosineLeaf284Bridge (iOf jOf)
open DSHTerminalBatchL0G1Zplus984 (PA PB slopeQ interQ pair_minorant)
open Terminal562Oracle (W W_nonneg W_field10)
set_option maxRecDepth 10000
def cl : ℚ := ∑ k : Fin 36, W k*slopeQ k*((iOf k).val-(jOf k).val : ℚ)
def f0 : ℚ := ∑ k : Fin 36,
  W k*(slopeQ k*((iOf k).val-(jOf k).val : ℚ)*LQ+interQ k)
def g (q : Fin 9) : ℚ := ∑ k : Fin 36,
  if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val then W k*slopeQ k else 0

theorem cl_nonpos : cl ≤ 0 := by decide +kernel
theorem f0_lower : (14441 : ℚ)/100000 < f0 := by decide +kernel
theorem g_nonneg : ∀ q : Fin 9, 0 ≤ g q := by decide +kernel

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
    rw [zval_eq,tval_sub y (Nat.le_of_lt (Terminal984Angles.pair_order k))]
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
    (14441 : ℝ)/100000 < affine y := by
  have hg : 0 ≤ ∑ q : Fin 9,(g q : ℝ)*y q :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (by exact_mod_cast g_nonneg q) (hy0 q))
  have hc : 0 ≤ (cl : ℝ)*(Lc-(LQ : ℝ)) :=
    mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast cl_nonpos)
      (sub_nonpos.mpr L_mem.2)
  have hD0 : 0 ≤ Dc := le_trans (by exact_mod_cast Dq_pos.le) D_mem.1
  have hf : (14441 : ℝ)/100000 < (f0 : ℝ) := by
    have h : ((14441/100000 : ℚ) : ℝ) < (f0 : ℝ) := Rat.cast_lt.mpr f0_lower
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  rw [affine_identity]
  linarith [mul_nonneg hD0 hg]

theorem energy_gt_on_cell (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 < energy y := by
  have hz := Terminal984Angles.angles_in_cell y hy0 hcell
  have hle : affine y ≤ energy y := Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_left (pair_minorant k _ (hz k))
      (by exact_mod_cast W_nonneg k))
  have ht : (FlashCosineLeaf284Bridge.T : ℝ)^2 < (14441 : ℝ)/100000 := by
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
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      ResumeNetwork.V2 (fun j => circleMap (theta y j)) :=
  (energy_gt_on_cell y hy0 hcell).trans_le (energy_le_oracle y)

theorem radius_gt (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hcell : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
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


theorem common_chart_oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2<
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have h := oracle_gt y hy0 hc
  rw [EnergyCommonChart.anchors_identity] at h
  exact h

theorem common_chart_radius (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 984)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r := by
  have h := radius_gt y hy0 hc C Z r
    (by rw [EnergyCommonChart.anchors_identity]; exact hf)
  exact Terminal562Oracle.sourceRadius_lt_T.trans h

theorem terminal984 : (DBMSourceTree.data (984 : Fin 5011)).terminal=true := by decide +kernel
theorem wrong_cell_rejected :
    (DBMSourceTree.data (984 : Fin 5011)).db≠(DBMSourceTree.data (562 : Fin 5011)).db := by
  decide +kernel

end N11Formalization.Terminal984Oracle
#check @N11Formalization.Terminal984Oracle.energy_gt_on_cell
#check @N11Formalization.Terminal984Oracle.energy_le_oracle
#check @N11Formalization.Terminal984Oracle.common_chart_radius
#print axioms N11Formalization.Terminal984Oracle.energy_gt_on_cell
#print axioms N11Formalization.Terminal984Oracle.common_chart_radius
