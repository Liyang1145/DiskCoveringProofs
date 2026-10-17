import N11Formalization.DBMAngleProvider
import N11Formalization.Terminal2162Minorants
import N11Formalization.Terminal2166Angles

/-! Actual instances of the convex/DBM core: NEW terminal2162 and a
nonzero real DBM dual for already-paid2166. No numeric/field/angle premise. -/
set_option autoImplicit false
namespace N11Formalization.TerminalDualConsumers
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.FlashCosineLeaf284Bridge (iOf jOf)
open _root_.N11Formalization.ConvexMinorantCore
open _root_.N11Formalization.DBMMinorantDual
open _root_.N11Formalization.Terminal562Oracle (W W_nonneg)
noncomputable section
set_option maxRecDepth 10000

def b : Fin 7 → ℚ := ![1,0,0,0,0,0,0]
theorem b_nonneg : ∀ f : Fin 7,0≤b f := by decide +kernel
theorem b_sum : (∑ f : Fin 7,b f)=1 := by decide +kernel
theorem W_mix : ∀ k : Fin 36,W k ≤ mixWeight b k := by decide +kernel

namespace Own2162
open _root_.N11Formalization.Terminal2162Minorants (PA PB slopeQ interQ pair_minorant)

def rowFrom : Fin 0 → Fin 10 := Fin.elim0
def rowTo : Fin 0 → Fin 10 := Fin.elim0
def lam : Fin 0 → ℚ := Fin.elim0
theorem lam_nonneg : ∀ a : Fin 0,0≤lam a := by intro a; exact Fin.elim0 a
theorem reduced : ∀ q : Fin 9,
    (0 : ℚ)≤endpointLo Dq DQ (g W slopeQ q)+rho rowFrom rowTo lam q := by decide +kernel
theorem numeric_check :
    FlashCosineLeaf284Bridge.T^2 < lower W slopeQ interQ 2162 rowFrom rowTo lam 0 := by
  decide +kernel
theorem endpoint_binding : ∀ k : Fin 36,
    PA k≤((iOf k).val-(jOf k).val : ℚ)*LQ+Dq*DBMAngleProvider.slo 2162 k ∧
    ((iOf k).val-(jOf k).val : ℚ)*Lq+DQ*DBMAngleProvider.shi 2162 k≤PB k := by
  decide +kernel
theorem angles_in_cell (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2162)
      (FlashLeafSplit.tlift y)) :
    ∀ k,zval y (iOf k) (jOf k)∈Set.Icc (PA k : ℝ) (PB k : ℝ) :=
  DBMAngleProvider.angles_of_endpoints 2162 PA PB endpoint_binding y hy0 hc

theorem affine_strict (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2162)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 < affine W slopeQ interQ y := by
  have hn : (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      (lower W slopeQ interQ 2162 rowFrom rowTo lam 0 : ℝ) := by exact_mod_cast numeric_check
  exact hn.trans_le
    (affine_lower_of_dual W slopeQ interQ 2162 rowFrom rowTo lam 0 lam_nonneg reduced y hy0 hy1 hc)

theorem oracle_gt (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2162)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  (affine_strict y hy0 hy1 hc).trans_le
    (affine_le_oracle b W slopeQ interQ PA PB b_nonneg b_sum W_nonneg W_mix pair_minorant
      y (angles_in_cell y hy0 hc))

theorem common_chart_radius (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2162)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  radius_of_dual b W slopeQ interQ PA PB 2162 rowFrom rowTo lam 0
    b_nonneg b_sum W_nonneg W_mix pair_minorant lam_nonneg reduced numeric_check
    y hy0 hy1 hc (angles_in_cell y hy0 hc) C Z r hf
theorem terminal : (DBMSourceTree.data (2162 : Fin 5011)).terminal=true := by decide +kernel
end Own2162

namespace Own2166
open _root_.N11Formalization.DSHTerminalBatchL0G1Zplus2166 (PA PB slopeQ interQ pair_minorant)
def rowFrom : Fin 1 → Fin 10 := fun _ => 4
def rowTo : Fin 1 → Fin 10 := fun _ => 3
def lam : Fin 1 → ℚ := fun _ => Dq*g W slopeQ 3
theorem lam_nonneg : ∀ a : Fin 1,0≤lam a := by decide +kernel
theorem lam_pos : (0 : ℚ)<lam 0 := by decide +kernel
theorem reduced : ∀ q : Fin 9,
    (0 : ℚ)≤endpointLo Dq DQ (g W slopeQ q)+rho rowFrom rowTo lam q := by decide +kernel
theorem numeric_check :
    FlashCosineLeaf284Bridge.T^2 < lower W slopeQ interQ 2166 rowFrom rowTo lam 0 := by
  decide +kernel
theorem zero_dual_fails :
    ¬(FlashCosineLeaf284Bridge.T^2 <
      lower W slopeQ interQ 2166 rowFrom rowTo (fun _ => 0) 0) := by decide +kernel
theorem common_chart_radius (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 2166)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  radius_of_dual b W slopeQ interQ PA PB 2166 rowFrom rowTo lam 0
    b_nonneg b_sum W_nonneg W_mix pair_minorant lam_nonneg reduced numeric_check
    y hy0 hy1 hc (Terminal2166Angles.angles_in_cell y hy0 hc) C Z r hf
end Own2166

end
end N11Formalization.TerminalDualConsumers
#check @N11Formalization.TerminalDualConsumers.Own2162.endpoint_binding
#check @N11Formalization.TerminalDualConsumers.Own2162.affine_strict
#check @N11Formalization.TerminalDualConsumers.Own2162.common_chart_radius
#check @N11Formalization.TerminalDualConsumers.Own2166.lam_pos
#check @N11Formalization.TerminalDualConsumers.Own2166.zero_dual_fails
#check @N11Formalization.TerminalDualConsumers.Own2166.common_chart_radius
#print axioms N11Formalization.TerminalDualConsumers.Own2162.common_chart_radius
#print axioms N11Formalization.TerminalDualConsumers.Own2166.common_chart_radius
