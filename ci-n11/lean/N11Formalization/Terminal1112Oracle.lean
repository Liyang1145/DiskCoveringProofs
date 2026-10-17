import N11Formalization.Terminal1112Angles
import N11Formalization.Field10MinorantCore

/-! OWN1112 minorant/actualcell numeric providers to shared actualfield10 core.
No minorant/domain/energy/field/oracle premise in final radiusconsumer. -/
set_option autoImplicit false
namespace N11Formalization.Terminal1112Oracle
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.DSHTerminalBatchL0G1Zplus1112 (PA PB slopeQ interQ pair_minorant)
open _root_.N11Formalization.Field10MinorantCore
set_option maxRecDepth 10000
noncomputable section
theorem cl_nonpos : cl slopeQ≤0 := by decide +kernel
theorem f0_lower : (14441 : ℚ)/100000<f0 slopeQ interQ := by decide +kernel
theorem g_nonneg : ∀ q : Fin 9,0≤g slopeQ q := by decide +kernel

theorem affine_strict (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 1112)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2<affine slopeQ interQ y := by
  have hF : (14441 : ℝ)/100000<(f0 slopeQ interQ : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr f0_lower
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  have hg : (0 : ℝ)≤∑ q : Fin 9,(g slopeQ q : ℝ)*y q :=
    g_sum_nonneg slopeQ g_nonneg y hy0
  have h := affine_lower slopeQ interQ y cl_nonpos (14441/100000) (0) hF (by norm_num) hg
  have ht : (FlashCosineLeaf284Bridge.T : ℝ)^2<14441/100000+(7/10)*(0) := by
    norm_num [FlashCosineLeaf284Bridge.T]
  exact ht.trans h

theorem oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 1112)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2<ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  (affine_strict y hy0 hc).trans_le (affine_le_oracle slopeQ interQ PA PB pair_minorant
    y (Terminal1112Angles.angles_in_cell y hy0 hc))

theorem common_chart_radius (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 1112)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r :=
  radius_of_minorants slopeQ interQ PA PB pair_minorant y
    (Terminal1112Angles.angles_in_cell y hy0 hc) (affine_strict y hy0 hc) C Z r hf

theorem terminal : (DBMSourceTree.data (1112 : Fin 5011)).terminal=true := by decide +kernel
end
end N11Formalization.Terminal1112Oracle
#check @N11Formalization.Terminal1112Oracle.affine_strict
#check @N11Formalization.Terminal1112Oracle.oracle_gt
#check @N11Formalization.Terminal1112Oracle.common_chart_radius
#print axioms N11Formalization.Terminal1112Oracle.common_chart_radius
