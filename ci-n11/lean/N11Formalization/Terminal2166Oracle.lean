import N11Formalization.Terminal2166Angles
import N11Formalization.Field10MinorantCore

/-! OWN2166 minorant/actualcell numeric providers to shared actualfield10 core.
No minorant/domain/energy/field/oracle premise in final radiusconsumer. -/
set_option autoImplicit false
namespace N11Formalization.Terminal2166Oracle
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.DSHTerminalBatchL0G1Zplus2166 (PA PB slopeQ interQ pair_minorant)
open _root_.N11Formalization.Field10MinorantCore
set_option maxRecDepth 10000
noncomputable section
theorem cl_nonpos : cl slopeQ≤0 := by decide +kernel
theorem f0_lower : (14438 : ℚ)/100000<f0 slopeQ interQ := by decide +kernel
theorem g_nonneg : ∀ q : Fin 9,0≤g slopeQ q := by decide +kernel

theorem g3_lower : (1/10000 : ℚ)≤g slopeQ 3 := by decide +kernel
theorem y3_lower (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) : (1/4 : ℝ)≤y 3 := by
  have h := hc 4 3
  have he : (DBMSourceTree.data (2166 : Fin 5011)).db 4 3=(-1024 : ℤ) := by decide +kernel
  simp only [DBMTreeKernel.matrix,he] at h
  have ht : FlashLeafSplit.tlift y 4-FlashLeafSplit.tlift y 3=y 3 := by
    rw [← FlashCosineLeaf284Bridge.tval_eq_tlift,← FlashCosineLeaf284Bridge.tval_eq_tlift,
      tval_sub y (show (3 : ℕ)≤4 by decide)]
    change (∑ q : Fin 9, if (3 : ℕ)≤q.val ∧ q.val < 4 then y q else 0)=y 3
    have heq : (fun q : Fin 9 => if (3 : ℕ)≤q.val ∧ q.val < 4 then y q else 0)=
        fun q : Fin 9 => if q=3 then y q else 0 := by
      funext q
      fin_cases q <;> simp
    rw [heq]
    simp
  norm_num at h
  linarith
theorem g_sum_lower (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) : (1/40000 : ℝ)≤∑ q : Fin 9,(g slopeQ q : ℝ)*y q := by
  have hga : (1/10000 : ℝ)≤(g slopeQ 3 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr g3_lower
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have h := g_sum_single_lower slopeQ g_nonneg y hy0 3 (1/10000) (1/4)
    (by norm_num) (by norm_num) hga (y3_lower y hc)
  norm_num at h ⊢
  exact h

theorem affine_strict (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2<affine slopeQ interQ y := by
  have hF : (14438 : ℝ)/100000<(f0 slopeQ interQ : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr f0_lower
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  have hg : (1/40000 : ℝ)≤∑ q : Fin 9,(g slopeQ q : ℝ)*y q :=
    g_sum_lower y hy0 hc
  have h := affine_lower slopeQ interQ y cl_nonpos (14438/100000) (1/40000) hF (by norm_num) hg
  have ht : (FlashCosineLeaf284Bridge.T : ℝ)^2<14438/100000+(7/10)*(1/40000) := by
    norm_num [FlashCosineLeaf284Bridge.T]
  exact ht.trans h

theorem oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2<ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  (affine_strict y hy0 hc).trans_le (affine_le_oracle slopeQ interQ PA PB pair_minorant
    y (Terminal2166Angles.angles_in_cell y hy0 hc))

theorem common_chart_radius (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r :=
  radius_of_minorants slopeQ interQ PA PB pair_minorant y
    (Terminal2166Angles.angles_in_cell y hy0 hc) (affine_strict y hy0 hc) C Z r hf

theorem terminal : (DBMSourceTree.data (2166 : Fin 5011)).terminal=true := by decide +kernel
end
end N11Formalization.Terminal2166Oracle
#check @N11Formalization.Terminal2166Oracle.affine_strict
#check @N11Formalization.Terminal2166Oracle.oracle_gt
#check @N11Formalization.Terminal2166Oracle.common_chart_radius
#print axioms N11Formalization.Terminal2166Oracle.common_chart_radius
