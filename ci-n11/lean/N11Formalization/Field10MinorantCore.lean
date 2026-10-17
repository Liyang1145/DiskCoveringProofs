import N11Formalization.Terminal984Oracle

/-! Shared actual-field semantic consumer for per-node minorant providers.
Field10's normalized canonical51 oracle proof is paid, not a supplied weight/
Gram/energy hypothesis. Per-node numeric and interval inputs remain explicit
until instantiated. This is not a theorem about arbitrary disk Covers. -/
set_option autoImplicit false
namespace N11Formalization.Field10MinorantCore
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.FlashCosineLeaf284Bridge (iOf jOf)
open _root_.N11Formalization.Terminal562Oracle (W W_nonneg)
noncomputable section

def cl (s : Fin 36 → ℚ) : ℚ :=
  ∑ k : Fin 36,W k*s k*((iOf k).val-(jOf k).val : ℚ)
def f0 (s c : Fin 36 → ℚ) : ℚ :=
  ∑ k : Fin 36,W k*(s k*((iOf k).val-(jOf k).val : ℚ)*LQ+c k)
def g (s : Fin 36 → ℚ) (q : Fin 9) : ℚ :=
  ∑ k : Fin 36,if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val then W k*s k else 0
def affine (s c : Fin 36 → ℚ) (y : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 36,(W k : ℝ)*((s k : ℝ)*zval y (iOf k) (jOf k)+(c k : ℝ))

theorem affine_identity (s c : Fin 36 → ℚ) (y : Fin 9 → ℝ) :
    affine s c y=(f0 s c : ℝ)+(cl s : ℝ)*(Lc-(LQ : ℝ))+
      Dc*(∑ q : Fin 9,(g s q : ℝ)*y q) := by
  have he (k : Fin 36) :
      zval y (iOf k) (jOf k)=
        ((iOf k).val-(jOf k).val : ℝ)*Lc+
          Dc*(∑ q : Fin 9,if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val then y q else 0) := by
    rw [zval_eq,tval_sub y (Nat.le_of_lt (Terminal562SimplexEnergy.pair_order k))]
    rfl
  have hg : Dc*(∑ q : Fin 9,(g s q : ℝ)*y q)=
      ∑ k : Fin 36,(W k : ℝ)*(s k : ℝ)*Dc*
        (∑ q : Fin 9,if (iOf k).val ≤ q.val ∧ q.val < (jOf k).val then y q else 0) := by
    unfold g
    push_cast
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : (iOf k).val ≤ q.val ∧ q.val < (jOf k).val
    · simp only [if_pos h,Rat.cast_mul]; ring
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

theorem g_sum_nonneg (s : Fin 36 → ℚ) (hgn : ∀ q,0≤g s q)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) : 0≤∑ q : Fin 9,(g s q : ℝ)*y q :=
  Finset.sum_nonneg (fun q _ => mul_nonneg (by exact_mod_cast hgn q) (hy0 q))

/-- Retain one actual cell coordinate; avoids discarding the positive
coefficient contribution when a whole-simplex floor alone is insufficient. -/
theorem g_sum_single_lower (s : Fin 36 → ℚ) (hgn : ∀ q,0≤g s q)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (q : Fin 9) (a b : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hga : a≤(g s q : ℝ)) (hyb : b≤y q) :
    a*b≤∑ j : Fin 9,(g s j : ℝ)*y j := by
  apply (mul_le_mul hga hyb hb (by exact_mod_cast hgn q)).trans
  have hn (j : Fin 9) (_ : j∈(Finset.univ : Finset (Fin 9))) :
      (0 : ℝ)≤(g s j : ℝ)*y j :=
    mul_nonneg (by exact_mod_cast hgn j) (hy0 j)
  exact Finset.single_le_sum hn (Finset.mem_univ q)

theorem D_ge_seven_tenths : (7/10 : ℝ)≤Dc := by
  exact (by norm_num [Dq,Lq,RatInterval.piHi] : (7/10 : ℝ)≤(Dq : ℝ)).trans D_mem.1

theorem affine_lower (s c : Fin 36 → ℚ) (y : Fin 9 → ℝ)
    (hcl : cl s≤0) (F B : ℝ) (hF : F<(f0 s c : ℝ))
    (hB : 0≤B) (hg : B≤∑ q : Fin 9,(g s q : ℝ)*y q) :
    F+(7/10)*B<affine s c y := by
  have hc : 0≤(cl s : ℝ)*(Lc-(LQ : ℝ)) :=
    mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast hcl) (sub_nonpos.mpr L_mem.2)
  have hm := mul_le_mul D_ge_seven_tenths hg hB (by linarith [D_ge_seven_tenths])
  rw [affine_identity]
  linarith

/-- True bound direction: minorants<=actual weightedenergy<=field10<=V2.
No external weight/oracle premise; node-specific minorants/domains explicit. -/
theorem affine_le_oracle (s c A B : Fin 36 → ℚ)
    (hminor : ∀ k,∀ z∈Set.Icc (A k : ℝ) (B k : ℝ),
      (s k : ℝ)*z+(c k : ℝ)≤1-Real.cos z)
    (y : Fin 9 → ℝ)
    (hz : ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (A k : ℝ) (B k : ℝ)) :
    affine s c y≤ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have he : affine s c y≤Terminal984Oracle.energy y :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (hminor k _ (hz k)) (by exact_mod_cast W_nonneg k))
  have hu := Terminal984Oracle.energy_le_oracle y
  rw [EnergyCommonChart.anchors_identity] at hu
  exact he.trans hu

theorem radius_of_minorants (s c A B : Fin 36 → ℚ)
    (hminor : ∀ k,∀ z∈Set.Icc (A k : ℝ) (B k : ℝ),
      (s k : ℝ)*z+(c k : ℝ)≤1-Real.cos z)
    (y : Fin 9 → ℝ)
    (hz : ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (A k : ℝ) (B k : ℝ))
    (hstrict : (FlashCosineLeaf284Bridge.T : ℝ)^2<affine s c y)
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r := by
  have hlo := hstrict.trans_le (affine_le_oracle s c A B hminor y hz)
  have hhi := ResumeNetwork.oracle_le_feasible hf
  have ht : (0 : ℝ)≤FlashCosineLeaf284Bridge.T := by norm_num [FlashCosineLeaf284Bridge.T]
  have hT : (FlashCosineLeaf284Bridge.T : ℝ)<r := by nlinarith [hf.1]
  exact Terminal562Oracle.sourceRadius_lt_T.trans hT

end
end N11Formalization.Field10MinorantCore
#check @N11Formalization.Field10MinorantCore.affine_lower
#check @N11Formalization.Field10MinorantCore.affine_le_oracle
#check @N11Formalization.Field10MinorantCore.radius_of_minorants
#print axioms N11Formalization.Field10MinorantCore.radius_of_minorants
