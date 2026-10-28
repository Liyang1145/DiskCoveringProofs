import N11Formalization.CertifiedHarmonicField
import N11Formalization.DBMMinorantDual

/-! ANY finite family of genuinely Valid canonical51 harmonic packets.
Field/numeric/minorant/domain inputs stay explicit until concrete kernel
instantiation. No recorded field ID or solver value establishes Valid. -/
set_option autoImplicit false
namespace N11Formalization.CertifiedFieldMixtures
open Finset FlashCosine
open FlashCosineLeaf284Bridge (iOf jOf)
open CertifiedHarmonicField (Packet Valid)
noncomputable section

def weightQ (p : Packet) (k : Fin 36) : ℚ :=
  (CertifiedHarmonicField.wNum p k : ℚ)/(CertifiedHarmonicField.wDen p k : ℚ)
def mixWeight {n : ℕ} (p : Fin n → Packet) (b : Fin n → ℚ) (k : Fin 36) : ℚ :=
  ∑ f : Fin n,b f*2*weightQ (p f) k
theorem mixWeight_cast {n : ℕ} (p : Fin n → Packet) (b : Fin n → ℚ) (k : Fin 36) :
    (mixWeight p b k : ℝ)=
      ∑ f : Fin n,(b f : ℝ)*2*CertifiedHarmonicField.weight (p f) k := by
  simp only [mixWeight,weightQ,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_intCast,CertifiedHarmonicField.weight]
theorem energy_eq_mixture {n : ℕ} (p : Fin n → Packet) (b : Fin n → ℚ)
    (y : Fin 9 → ℝ) :
    ConvexMinorantCore.weightedEnergy (mixWeight p b) y =
      ∑ f : Fin n,(b f : ℝ)*CertifiedHarmonicField.fieldEnergy (p f) (theta y) := by
  unfold ConvexMinorantCore.weightedEnergy
  simp_rw [mixWeight_cast]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp only [CertifiedHarmonicField.fieldEnergy,Finset.mul_sum,zval]
  apply Finset.sum_congr rfl
  intro k _
  ring
theorem weightedEnergy_le_oracle {n : ℕ}
    (p : Fin n → Packet) (hp : ∀ f,Valid (p f)) (b : Fin n → ℚ)
    (w : Fin 36 → ℚ) (hb0 : ∀ f,0 ≤ b f) (hb1 : ∑ f,b f=1)
    (hw : ∀ k,w k ≤ mixWeight p b k) (y : Fin 9 → ℝ) :
    ConvexMinorantCore.weightedEnergy w y ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have he : ConvexMinorantCore.weightedEnergy w y ≤
      ConvexMinorantCore.weightedEnergy (mixWeight p b) y :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
      (by exact_mod_cast hw k) (by linarith [Real.cos_le_one (zval y (iOf k) (jOf k))]))
  have hm : ConvexMinorantCore.weightedEnergy (mixWeight p b) y ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
    rw [energy_eq_mixture]
    calc
      _ ≤ ∑ f : Fin n,(b f : ℝ)*
          ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
        Finset.sum_le_sum (fun f _ => mul_le_mul_of_nonneg_left
          (CertifiedHarmonicField.chart_energy_le_oracle (p f) (hp f) y)
          (by exact_mod_cast hb0 f))
      _ = _ := by
        rw [← Finset.sum_mul]
        have h : (∑ f : Fin n,(b f : ℝ))=1 := by exact_mod_cast hb1
        rw [h,one_mul]
  exact he.trans hm
theorem affine_le_oracle {n : ℕ}
    (p : Fin n → Packet) (hp : ∀ f,Valid (p f)) (b : Fin n → ℚ)
    (w s c A B : Fin 36 → ℚ) (hb0 : ∀ f,0 ≤ b f) (hb1 : ∑ f,b f=1)
    (hw0 : ∀ k,0 ≤ w k) (hw : ∀ k,w k ≤ mixWeight p b k)
    (hminor : ∀ k,∀ z∈Set.Icc (A k : ℝ) (B k : ℝ),
      (s k : ℝ)*z+(c k : ℝ) ≤ 1-Real.cos z)
    (y : Fin 9 → ℝ)
    (hz : ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (A k : ℝ) (B k : ℝ)) :
    ConvexMinorantCore.affine w s c y ≤
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have he : ConvexMinorantCore.affine w s c y ≤
      ConvexMinorantCore.weightedEnergy w y :=
    Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (hminor k _ (hz k)) (by exact_mod_cast hw0 k))
  exact he.trans (weightedEnergy_le_oracle p hp b w hb0 hb1 hw y)
theorem radius_of_dual {n m : ℕ}
    (p : Fin n → Packet) (hp : ∀ f,Valid (p f)) (b : Fin n → ℚ)
    (w s c A B : Fin 36 → ℚ) (node : Fin 5011)
    (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (rmin : ℚ)
    (hb0 : ∀ f,0 ≤ b f) (hb1 : ∑ f,b f=1)
    (hw0 : ∀ k,0 ≤ w k) (hw : ∀ k,w k ≤ mixWeight p b k)
    (hminor : ∀ k,∀ z∈Set.Icc (A k : ℝ) (B k : ℝ),
      (s k : ℝ)*z+(c k : ℝ) ≤ 1-Real.cos z)
    (hlam : ∀ a,0 ≤ lam a)
    (hr : ∀ q : Fin 9,rmin ≤ ConvexMinorantCore.endpointLo Dq DQ
      (ConvexMinorantCore.g w s q)+DBMMinorantDual.rho rowFrom rowTo lam q)
    (hcheck : FlashCosineLeaf284Bridge.T^2 <
      DBMMinorantDual.lower w s c node rowFrom rowTo lam rmin)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 node)
      (FlashLeafSplit.tlift y))
    (hz : ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (A k : ℝ) (B k : ℝ))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  have hnum : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      (DBMMinorantDual.lower w s c node rowFrom rowTo lam rmin : ℝ) := by
    exact_mod_cast hcheck
  have hlo := hnum.trans_le
    (DBMMinorantDual.affine_lower_of_dual w s c node rowFrom rowTo lam rmin
      hlam hr y hy0 hy1 hc)
  have ho := hlo.trans_le (affine_le_oracle p hp b w s c A B hb0 hb1 hw0 hw hminor y hz)
  have hhi := ResumeNetwork.oracle_le_feasible hf
  have ht : (0 : ℝ) ≤ FlashCosineLeaf284Bridge.T := by
    norm_num [FlashCosineLeaf284Bridge.T]
  have hT : (FlashCosineLeaf284Bridge.T : ℝ) < r := by nlinarith [hf.1]
  exact Terminal562Oracle.sourceRadius_lt_T.trans hT

end
end N11Formalization.CertifiedFieldMixtures
#check @N11Formalization.CertifiedFieldMixtures.weightedEnergy_le_oracle
#check @N11Formalization.CertifiedFieldMixtures.radius_of_dual
#print axioms N11Formalization.CertifiedFieldMixtures.weightedEnergy_le_oracle
#print axioms N11Formalization.CertifiedFieldMixtures.radius_of_dual
