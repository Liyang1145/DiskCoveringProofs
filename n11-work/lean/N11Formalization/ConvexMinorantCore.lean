import N11Formalization.Field10MinorantCore

/-! Actual seven normalized canonical51 fields, arbitrary rational convex
mixtures and rounded-down weights. Signed affine coefficients are retained.
Numeric/per-node minorant inputs remain explicit until kernel instantiated. -/
set_option autoImplicit false
namespace N11Formalization.ConvexMinorantCore
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.FlashCosineLeaf284Bridge (iOf jOf)
noncomputable section

def weightQ (f : Fin 7) (k : Fin 36) : ℚ :=
  (Leaf4348Fields7.wNum f k : ℚ)/(Leaf4348Fields7.wDen f k : ℚ)
def mixWeight (b : Fin 7 → ℚ) (k : Fin 36) : ℚ :=
  ∑ f : Fin 7,b f*2*weightQ f k
def cl (w s : Fin 36 → ℚ) : ℚ :=
  ∑ k : Fin 36,w k*s k*((iOf k).val-(jOf k).val : ℚ)
def cv (w c : Fin 36 → ℚ) : ℚ := ∑ k : Fin 36,w k*c k
def g (w s : Fin 36 → ℚ) (q : Fin 9) : ℚ :=
  ∑ k : Fin 36,if (iOf k).val≤q.val ∧ q.val<(jOf k).val then w k*s k else 0
def endpointLo (a b x : ℚ) : ℚ := x*(if 0≤x then a else b)
def f0Lo (w s c : Fin 36 → ℚ) : ℚ :=
  cv w c+endpointLo Lq LQ (cl w s)
def affine (w s c : Fin 36 → ℚ) (y : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 36,(w k : ℝ)*((s k : ℝ)*zval y (iOf k) (jOf k)+(c k : ℝ))
def weightedEnergy (w : Fin 36 → ℚ) (y : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 36,(w k : ℝ)*(1-Real.cos (zval y (iOf k) (jOf k)))

theorem endpointLo_sound (a b x : ℚ) (t : ℝ)
    (ht : (a : ℝ)≤t ∧ t≤(b : ℝ)) : (endpointLo a b x : ℝ)≤(x : ℝ)*t := by
  by_cases hx : 0≤x
  · simp only [endpointLo,if_pos hx,Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left ht.1 (by exact_mod_cast hx)
  · simp only [endpointLo,if_neg hx,Rat.cast_mul]
    exact mul_le_mul_of_nonpos_left ht.2 (by exact_mod_cast (le_of_not_ge hx))

theorem affine_identity (w s c : Fin 36 → ℚ) (y : Fin 9 → ℝ) :
    affine w s c y=(cv w c : ℝ)+(cl w s : ℝ)*Lc+
      Dc*(∑ q : Fin 9,(g w s q : ℝ)*y q) := by
  have he (k : Fin 36) :
      zval y (iOf k) (jOf k)=
        ((iOf k).val-(jOf k).val : ℝ)*Lc+
          Dc*(∑ q : Fin 9,if (iOf k).val≤q.val ∧ q.val<(jOf k).val then y q else 0) := by
    rw [zval_eq,tval_sub y (Nat.le_of_lt (Terminal562SimplexEnergy.pair_order k))]
    rfl
  have hg : Dc*(∑ q : Fin 9,(g w s q : ℝ)*y q)=
      ∑ k : Fin 36,(w k : ℝ)*(s k : ℝ)*Dc*
        (∑ q : Fin 9,if (iOf k).val≤q.val ∧ q.val<(jOf k).val then y q else 0) := by
    unfold g
    push_cast
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : (iOf k).val≤q.val ∧ q.val<(jOf k).val
    · simp only [if_pos h,Rat.cast_mul]; ring
    · simp only [if_neg h,Rat.cast_zero,mul_zero,zero_mul]
  rw [hg]
  unfold affine cv cl
  push_cast
  simp_rw [he]
  simp only [Finset.sum_mul]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem affine_f0_lower (w s c : Fin 36 → ℚ) (y : Fin 9 → ℝ) :
    (f0Lo w s c : ℝ)+Dc*(∑ q : Fin 9,(g w s q : ℝ)*y q)≤affine w s c y := by
  have h := endpointLo_sound Lq LQ (cl w s) Lc L_mem
  rw [affine_identity]
  simp only [f0Lo,Rat.cast_add]
  linarith

theorem mixWeight_cast (b : Fin 7 → ℚ) (k : Fin 36) :
    (mixWeight b k : ℝ)=∑ f : Fin 7,(b f : ℝ)*2*Leaf4348Fields7.weight f k := by
  simp only [mixWeight,weightQ,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_intCast,Leaf4348Fields7.weight]

theorem energy_eq_mixture (b : Fin 7 → ℚ) (y : Fin 9 → ℝ) :
    weightedEnergy (mixWeight b) y=
      ∑ f : Fin 7,(b f : ℝ)*Leaf4348Fields7.fieldEnergy f (theta y) := by
  unfold weightedEnergy
  simp_rw [mixWeight_cast]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Leaf4348Fields7.fieldEnergy,Finset.mul_sum,zval]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem weightedEnergy_le_oracle (b : Fin 7 → ℚ) (w : Fin 36 → ℚ)
    (hb0 : ∀ f,0≤b f) (hb1 : ∑ f,b f=1)
    (hw : ∀ k,w k ≤ mixWeight b k) (y : Fin 9 → ℝ) :
    weightedEnergy w y≤ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have he : weightedEnergy w y≤weightedEnergy (mixWeight b) y :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
      (by exact_mod_cast hw k) (by linarith [Real.cos_le_one (zval y (iOf k) (jOf k))]))
  have hm : weightedEnergy (mixWeight b) y≤
      ResumeNetwork.V2 (fun j => N11Formalization.circleMap (theta y j)) := by
    rw [energy_eq_mixture]
    calc
      _ ≤ ∑ f : Fin 7,(b f : ℝ)*
          ResumeNetwork.V2 (fun j => N11Formalization.circleMap (theta y j)) :=
        Finset.sum_le_sum (fun f _ => mul_le_mul_of_nonneg_left
          (Leaf4348Fields7.source_energy_le_oracle f (theta y)) (by exact_mod_cast hb0 f))
      _ = _ := by
        rw [← Finset.sum_mul]
        have h : (∑ f : Fin 7,(b f : ℝ))=1 := by exact_mod_cast hb1
        rw [h,one_mul]
  rw [EnergyCommonChart.anchors_identity] at hm
  exact he.trans hm

theorem affine_le_oracle (b : Fin 7 → ℚ) (w s c A B : Fin 36 → ℚ)
    (hb0 : ∀ f,0≤b f) (hb1 : ∑ f,b f=1)
    (hw0 : ∀ k,0≤w k) (hw : ∀ k,w k ≤ mixWeight b k)
    (hminor : ∀ k,∀ z∈Set.Icc (A k : ℝ) (B k : ℝ),
      (s k : ℝ)*z+(c k : ℝ)≤1-Real.cos z)
    (y : Fin 9 → ℝ)
    (hz : ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (A k : ℝ) (B k : ℝ)) :
    affine w s c y≤ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have he : affine w s c y≤weightedEnergy w y :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (hminor k _ (hz k)) (by exact_mod_cast hw0 k))
  exact he.trans (weightedEnergy_le_oracle b w hb0 hb1 hw y)

theorem radius_of_minorants (b : Fin 7 → ℚ) (w s c A B : Fin 36 → ℚ)
    (hb0 : ∀ f,0≤b f) (hb1 : ∑ f,b f=1)
    (hw0 : ∀ k,0≤w k) (hw : ∀ k,w k ≤ mixWeight b k)
    (hminor : ∀ k,∀ z∈Set.Icc (A k : ℝ) (B k : ℝ),
      (s k : ℝ)*z+(c k : ℝ)≤1-Real.cos z)
    (y : Fin 9 → ℝ)
    (hz : ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (A k : ℝ) (B k : ℝ))
    (hstrict : (FlashCosineLeaf284Bridge.T : ℝ)^2<affine w s c y)
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r := by
  have hlo := hstrict.trans_le (affine_le_oracle b w s c A B hb0 hb1 hw0 hw hminor y hz)
  have hhi := ResumeNetwork.oracle_le_feasible hf
  have ht : (0 : ℝ)≤FlashCosineLeaf284Bridge.T := by norm_num [FlashCosineLeaf284Bridge.T]
  have hT : (FlashCosineLeaf284Bridge.T : ℝ)<r := by nlinarith [hf.1]
  exact Terminal562Oracle.sourceRadius_lt_T.trans hT

end
end N11Formalization.ConvexMinorantCore
#check @N11Formalization.ConvexMinorantCore.affine_identity
#check @N11Formalization.ConvexMinorantCore.weightedEnergy_le_oracle
#check @N11Formalization.ConvexMinorantCore.radius_of_minorants
#print axioms N11Formalization.ConvexMinorantCore.weightedEnergy_le_oracle
#print axioms N11Formalization.ConvexMinorantCore.radius_of_minorants
