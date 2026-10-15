import N11Formalization.HarmonicFieldsB02
import N11Formalization.Terminal4265Packet

/-! OWN4265 actual7-field radius consumer. All actual field-validity,
normalization, rounded-weight, interval, continuum and dual inputs are paid.
The arbitrary-Covers-to-chart/Feasible reduction is NOT proved here. -/
set_option autoImplicit false
namespace N11Formalization.Terminal4265Consumer
open Finset FlashCosine ConvexMinorantCore DBMMinorantDual
open FlashCosineLeaf284Bridge (iOf jOf)
open Terminal4265Packet
noncomputable section
set_option maxRecDepth 10000

theorem rounded_le : ∀ f : Fin 7,∀ k : Fin 36,
    rounded f k ≤ 2*CertifiedFieldMixtures.weightQ (HarmonicFieldsB02.packet f) k := by
  decide +kernel
theorem W_mix (k : Fin 36) :
    W k ≤ CertifiedFieldMixtures.mixWeight HarmonicFieldsB02.packet beta k := by
  unfold W CertifiedFieldMixtures.mixWeight
  apply Finset.sum_le_sum
  intro f _
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (rounded_le f k) (beta_nonneg f)
theorem angles_in_cell (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 nodeID)
      (FlashLeafSplit.tlift y)) :
    ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (PA k : ℝ) (PB k : ℝ) :=
  DBMAngleProvider.angles_of_endpoints nodeID PA PB endpoint_binding y hy0 hc
theorem affine_strict (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 nodeID)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 < affine W slopeQ interQ y := by
  have hn : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      (lower W slopeQ interQ nodeID rowFrom rowTo lam rmin : ℝ) := by
    exact_mod_cast numeric_check
  exact hn.trans_le (affine_lower_of_dual W slopeQ interQ nodeID rowFrom rowTo lam rmin
    lam_nonneg reduced y hy0 hy1 hc)
theorem oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 nodeID)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  (affine_strict y hy0 hy1 hc).trans_le
    (CertifiedFieldMixtures.affine_le_oracle
      HarmonicFieldsB02.packet HarmonicFieldsB02.all_valid beta W slopeQ interQ PA PB
      beta_nonneg beta_sum W_nonneg W_mix pair_minorant y (angles_in_cell y hy0 hc))
theorem common_chart_radius (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 nodeID)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  CertifiedFieldMixtures.radius_of_dual
    HarmonicFieldsB02.packet HarmonicFieldsB02.all_valid beta W slopeQ interQ PA PB
    nodeID rowFrom rowTo lam rmin beta_nonneg beta_sum W_nonneg W_mix pair_minorant
    lam_nonneg reduced numeric_check y hy0 hy1 hc (angles_in_cell y hy0 hc) C Z r hf
end
end N11Formalization.Terminal4265Consumer
#check @N11Formalization.Terminal4265Consumer.rounded_le
#check @N11Formalization.Terminal4265Consumer.oracle_gt
#check @N11Formalization.Terminal4265Consumer.common_chart_radius
#print axioms N11Formalization.Terminal4265Consumer.oracle_gt
#print axioms N11Formalization.Terminal4265Consumer.common_chart_radius
