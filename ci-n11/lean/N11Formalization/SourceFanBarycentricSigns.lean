import N11Formalization.SourceFanConversion
import N11Formalization.SourceCentralGeometry

/-!
Exact source-box sign certificate for the remaining four fan barycentric
coefficients. The determinant-product intervals are built from the actual
Uvec/ring/hub expression-tree intervals; signs are kernel rational comparisons,
not host floats or intervals merely containing zero.
-/
set_option autoImplicit false
namespace N11Formalization.SourceFanBarycentricSigns
open N11Formalization RatInterval PinTangentGeometry SourceFanLengthCovector SourceFanConversion
noncomputable section

def normalPBox (k : Fin 9) (i : Fin 2) : RatInterval :=
  sub (ndUvecBox ndBox k i) (ndRingBox ndBox k i)
def normalQBox (k : Fin 9) (i : Fin 2) : RatInterval :=
  sub (ndUvecBox ndBox k i) (ndRingBox ndBox (k+1) i)
def hubBox (k : Fin 9) (i : Fin 2) : RatInterval :=
  if k=1 ∨ k=8 then ndHub1Box ndBox i else ndHub0Box ndBox i
def normalHBox (k : Fin 9) (i : Fin 2) : RatInterval :=
  sub (ndUvecBox ndBox k i) (hubBox k i)
def determinantBox (A B : Fin 2 → RatInterval) : RatInterval :=
  sub (mul (A 0) (B 1)) (mul (A 1) (B 0))
def productA (k : Fin 9) : RatInterval :=
  mul (determinantBox (normalHBox k) (normalQBox k))
    (determinantBox (normalPBox k) (normalQBox k))
def productB (k : Fin 9) : RatInterval :=
  mul (determinantBox (normalPBox k) (normalHBox k))
    (determinantBox (normalPBox k) (normalQBox k))

private theorem normalPBox_mem (k : Fin 9) (i : Fin 2) :
    (normalPBox k i).Mem (normalP k i) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact sub_mem (ndUvecBox_mem hb k i) (ndRingBox_mem hb k i)
private theorem normalQBox_mem (k : Fin 9) (i : Fin 2) :
    (normalQBox k i).Mem (normalQ k i) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact sub_mem (ndUvecBox_mem hb k i) (ndRingBox_mem hb (k+1) i)
private theorem normalHBox_mem (k : Fin 9) (i : Fin 2) :
    (normalHBox k i).Mem (normalH k i) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  have hh : (hubBox k i).Mem (sourceHub k i) := by
    unfold hubBox sourceHub
    split_ifs
    · exact ndHub1Box_mem hb i
    · exact ndHub0Box_mem hb i
  exact sub_mem (ndUvecBox_mem hb k i) hh

private theorem determinantBox_mem {A B : Fin 2 → RatInterval} {a b : Point}
    (hA : ∀ i, (A i).Mem (a i)) (hB : ∀ i, (B i).Mem (b i)) :
    (determinantBox A B).Mem (det a b) :=
  sub_mem (mul_mem (hA 0) (hB 1)) (mul_mem (hA 1) (hB 0))

private theorem productA_mem (k : Fin 9) :
    (productA k).Mem (det (normalH k) (normalQ k)*det (normalP k) (normalQ k)) :=
  mul_mem (determinantBox_mem (normalHBox_mem k) (normalQBox_mem k))
    (determinantBox_mem (normalPBox_mem k) (normalQBox_mem k))
private theorem productB_mem (k : Fin 9) :
    (productB k).Mem (det (normalP k) (normalH k)*det (normalP k) (normalQ k)) :=
  mul_mem (determinantBox_mem (normalPBox_mem k) (normalHBox_mem k))
    (determinantBox_mem (normalPBox_mem k) (normalQBox_mem k))

private theorem hubBox_two (i : Fin 2) : hubBox 2 i=ndHub0Box ndBox i := by
  simp [hubBox,Fin.ext_iff]
private theorem hubBox_three (i : Fin 2) : hubBox 3 i=ndHub0Box ndBox i := by
  simp [hubBox,Fin.ext_iff]

private theorem productA_read1 : (productA 1).hi<0 := by
  simp only [productA,determinantBox,normalPBox,normalQBox,normalHBox,hubBox]
  nd_eval
private theorem productB_read1 : (productB 1).hi<0 := by
  simp only [productB,determinantBox,normalPBox,normalQBox,normalHBox,hubBox]
  nd_eval
private theorem productA_read2 : (productA 2).hi<0 := by
  simp only [productA,determinantBox,normalPBox,normalQBox,normalHBox,hubBox_two]
  nd_eval
private theorem productB_read2 : (productB 2).hi<0 := by
  simp only [productB,determinantBox,normalPBox,normalQBox,normalHBox,hubBox_two]
  nd_eval
private theorem productA_read3 : (productA 3).hi<0 := by
  simp only [productA,determinantBox,normalPBox,normalQBox,normalHBox,hubBox_three]
  nd_eval
private theorem productB_read3 : (productB 3).hi<0 := by
  simp only [productB,determinantBox,normalPBox,normalQBox,normalHBox,hubBox_three]
  nd_eval
private theorem productA_read8 : (productA 8).hi<0 := by
  simp only [productA,determinantBox,normalPBox,normalQBox,normalHBox,hubBox]
  nd_eval
private theorem productB_read8 : (productB 8).hi<0 := by
  simp only [productB,determinantBox,normalPBox,normalQBox,normalHBox,hubBox]
  nd_eval

theorem product_bounds (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    (productA k).hi<0 ∧ (productB k).hi<0 := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨productA_read1,productB_read1⟩
  · exact ⟨productA_read2,productB_read2⟩
  · exact ⟨productA_read3,productB_read3⟩
  · exact ⟨productA_read8,productB_read8⟩

private theorem ratio_neg_of_product_neg (N D : ℝ) (hD : D≠0) (hND : N*D<0) :
    N/D<0 := by
  by_cases hp : 0<D
  · have hn : N<0 := by nlinarith
    exact div_neg_of_neg_of_pos hn hp
  · have hd : D<0 := lt_of_le_of_ne (le_of_not_gt hp) hD
    have hn : 0<N := by nlinarith
    exact div_neg_of_pos_of_neg hn hd

theorem sourceA_neg (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) : sourceA k<0 := by
  have hmem := (productA_mem k).2
  have hhi : ((productA k).hi : ℝ)<0 := by exact_mod_cast (product_bounds k hk).1
  exact ratio_neg_of_product_neg _ _
    (RootPinNormalConsumer.source_contact_normals_independent k hk) (lt_of_le_of_lt hmem hhi)

theorem sourceB_neg (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) : sourceB k<0 := by
  have hmem := (productB_mem k).2
  have hhi : ((productB k).hi : ℝ)<0 := by exact_mod_cast (product_bounds k hk).2
  exact ratio_neg_of_product_neg _ _
    (RootPinNormalConsumer.source_contact_normals_independent k hk) (lt_of_le_of_lt hmem hhi)

/-- Both formerly unpaid fan centre barycentric signs, with ACTUAL root-box
containment and strict determinant-product certificates discharged. -/
theorem source_betas_pos (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    0<betaP k ∧ 0<betaQ k ∧ 0<betaH k :=
  ⟨div_pos (neg_pos.mpr (sourceA_neg k hk)) (sourceConversion_pos k hk),
    div_pos (neg_pos.mpr (sourceB_neg k hk)) (sourceConversion_pos k hk),
    betaH_pos k hk⟩

def centralPBox (i : Fin 2) : RatInterval :=
  sub (ndWPointBox ndBox i) (ndHub0Box ndBox i)
def centralQBox (i : Fin 2) : RatInterval :=
  sub (ndWPointBox ndBox i) (ndHub1Box ndBox i)
def centralHBox (i : Fin 2) : RatInterval :=
  sub (ndWPointBox ndBox i) (ndRingBox ndBox 6 i)
def centralProductA : RatInterval :=
  mul (determinantBox centralHBox centralQBox) (determinantBox centralPBox centralQBox)
def centralProductB : RatInterval :=
  mul (determinantBox centralPBox centralHBox) (determinantBox centralPBox centralQBox)

private theorem centralPBox_mem (i : Fin 2) : (centralPBox i).Mem (SourceCentralGeometry.nP i) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact sub_mem (ndWPointBox_mem hb i) (ndHub0Box_mem hb i)
private theorem centralQBox_mem (i : Fin 2) : (centralQBox i).Mem (SourceCentralGeometry.nQ i) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact sub_mem (ndWPointBox_mem hb i) (ndHub1Box_mem hb i)
private theorem centralHBox_mem (i : Fin 2) : (centralHBox i).Mem (SourceCentralGeometry.nH i) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  exact sub_mem (ndWPointBox_mem hb i) (ndRingBox_mem hb 6 i)

private theorem centralProductA_mem :
    centralProductA.Mem (det SourceCentralGeometry.nH SourceCentralGeometry.nQ *
      det SourceCentralGeometry.nP SourceCentralGeometry.nQ) :=
  mul_mem (determinantBox_mem centralHBox_mem centralQBox_mem)
    (determinantBox_mem centralPBox_mem centralQBox_mem)
private theorem centralProductB_mem :
    centralProductB.Mem (det SourceCentralGeometry.nP SourceCentralGeometry.nH *
      det SourceCentralGeometry.nP SourceCentralGeometry.nQ) :=
  mul_mem (determinantBox_mem centralPBox_mem centralHBox_mem)
    (determinantBox_mem centralPBox_mem centralQBox_mem)

private theorem centralProductA_read : centralProductA.hi<0 := by
  simp only [centralProductA,determinantBox,centralPBox,centralQBox,centralHBox]
  nd_eval
private theorem centralProductB_read : centralProductB.hi<0 := by
  simp only [centralProductB,determinantBox,centralPBox,centralQBox,centralHBox]
  nd_eval

theorem centralA_neg : SourceCentralGeometry.a<0 := by
  have hmem := centralProductA_mem.2
  have hhi : (centralProductA.hi : ℝ)<0 := by exact_mod_cast centralProductA_read
  exact ratio_neg_of_product_neg _ _ SourceCentralGeometry.source_normals_independent
    (lt_of_le_of_lt hmem hhi)
theorem centralB_neg : SourceCentralGeometry.b<0 := by
  have hmem := centralProductB_mem.2
  have hhi : (centralProductB.hi : ℝ)<0 := by exact_mod_cast centralProductB_read
  exact ratio_neg_of_product_neg _ _ SourceCentralGeometry.source_normals_independent
    (lt_of_le_of_lt hmem hhi)

/-- The independently paid CENTRAL barycentric signs complete all five
representative triple signs; reflected source9-face transport remains separate. -/
theorem central_betas_pos :
    0<SourceCentralGeometry.betaP ∧ 0<SourceCentralGeometry.betaQ ∧ 0<SourceCentralGeometry.betaH :=
  ⟨div_pos (neg_pos.mpr centralA_neg) SourceCentralGeometry.conversion_pos,
    div_pos (neg_pos.mpr centralB_neg) SourceCentralGeometry.conversion_pos,
    div_pos (by norm_num) SourceCentralGeometry.conversion_pos⟩

end
end N11Formalization.SourceFanBarycentricSigns
#check @N11Formalization.SourceFanBarycentricSigns.source_betas_pos
#print axioms N11Formalization.SourceFanBarycentricSigns.source_betas_pos
#check @N11Formalization.SourceFanBarycentricSigns.central_betas_pos
#print axioms N11Formalization.SourceFanBarycentricSigns.central_betas_pos
