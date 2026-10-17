import N11Formalization.CuttingPlaneBatch7Packet

/-! Seven actual OWNcell/convexfield/fullDBM consumers, no packet/weight/
angle/dual/numeric/energy/oracle premise. ALL51Feasible domain retained. -/
set_option autoImplicit false
namespace N11Formalization.CuttingPlaneBatch7Consumer
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.FlashCosineLeaf284Bridge (iOf jOf)
open _root_.N11Formalization.ConvexMinorantCore
open _root_.N11Formalization.DBMMinorantDual
open _root_.N11Formalization.CuttingPlaneBatch7Packet
noncomputable section
set_option maxRecDepth 10000

theorem W_nonneg (i : Case) (k : Fin 36) : 0 ≤ W i k :=
  RoundedFieldWeights.mix_nonneg (beta i) (beta_nonneg i) k
theorem W_mix (i : Case) (k : Fin 36) : W i k ≤ mixWeight (beta i) k :=
  RoundedFieldWeights.mix_le (beta i) (beta_nonneg i) k
theorem angles_in_cell (i : Case) (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) :
    ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (PA i k : ℝ) (PB i k : ℝ) :=
  DBMAngleProvider.angles_of_endpoints (nodeID i) (PA i) (PB i) (endpoint_binding i) y hy0 hc
theorem affine_strict (i : Case) (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 < affine (W i) (slopeQ i) (interQ i) y := by
  have hn : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      (lower (W i) (slopeQ i) (interQ i) (nodeID i) (rowFrom i) (rowTo i) (lam i) (rmin i) : ℝ) := by
    exact_mod_cast numeric_check i
  exact hn.trans_le (affine_lower_of_dual (W i) (slopeQ i) (interQ i) (nodeID i)
    (rowFrom i) (rowTo i) (lam i) (rmin i) (lam_nonneg i) (reduced i) y hy0 hy1 hc)
theorem oracle_gt (i : Case) (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 < ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  (affine_strict i y hy0 hy1 hc).trans_le
    (affine_le_oracle (beta i) (W i) (slopeQ i) (interQ i) (PA i) (PB i)
      (beta_nonneg i) (beta_sum i) (W_nonneg i) (W_mix i) (pair_minorant i)
      y (angles_in_cell i y hy0 hc))
theorem common_chart_radius (i : Case) (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  radius_of_dual (beta i) (W i) (slopeQ i) (interQ i) (PA i) (PB i) (nodeID i)
    (rowFrom i) (rowTo i) (lam i) (rmin i) (beta_nonneg i) (beta_sum i)
    (W_nonneg i) (W_mix i) (pair_minorant i) (lam_nonneg i) (reduced i) (numeric_check i)
    y hy0 hy1 hc (angles_in_cell i y hy0 hc) C Z r hf

def newIDs : Finset (Fin 5011) := Finset.univ.image nodeID
theorem new_count : newIDs.card=7 := by decide +kernel
theorem node_injective : Function.Injective nodeID := by unfold Function.Injective; decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n∈newIDs) :
    (DBMSourceTree.data n).terminal=true := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
  exact terminal i
theorem new_radius (n : Fin 5011) (hn : n∈newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
  exact common_chart_radius i y hy0 hy1 hc C Z r hf
end
end N11Formalization.CuttingPlaneBatch7Consumer
#check @N11Formalization.CuttingPlaneBatch7Consumer.oracle_gt
#check @N11Formalization.CuttingPlaneBatch7Consumer.common_chart_radius
#check @N11Formalization.CuttingPlaneBatch7Consumer.new_count
#check @N11Formalization.CuttingPlaneBatch7Consumer.new_radius
#print axioms N11Formalization.CuttingPlaneBatch7Consumer.common_chart_radius
#print axioms N11Formalization.CuttingPlaneBatch7Consumer.new_radius
