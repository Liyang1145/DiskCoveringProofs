import N11Formalization.Patch120SharpDispatch
import N11Formalization.Leaf284TreeBridge
import N11Formalization.Leaf4348TreeBridge
import N11Formalization.Terminal562Oracle

/-! Existing genuine energy terminals on the SAME true chart used by ALL120
sharp cells. Threshold stays a proved strict bound above sourceRoot6.
No new terminal is counted; no other-terminal semantics is assumed paid. -/
set_option autoImplicit false
namespace N11Formalization.EnergyCommonChart
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

theorem actual_L : FlashCosine.Lc=Patch120K5Actual.L := by
  norm_num only [FlashCosine.Lc,Patch120K5Actual.L,Rat.cast_div,Rat.cast_ofNat]
theorem actual_D : FlashCosine.Dc=Patch120K5Actual.D := by
  rw [FlashCosine.Dc,actual_L]
  rfl
theorem theta_cellAngles (y : Fin 9 → ℝ) (j : Fin 9) :
    FlashCosine.theta y j=cellAngles y j := by
  rw [Leaf284TreeBridge.theta_eq_anchorAngle,actual_L,actual_D]
  rfl
theorem anchors_identity (y : Fin 9 → ℝ) :
    (fun j : Fin 9 => N11Formalization.circleMap (FlashCosine.theta y j))=chartAnchors y := by
  funext j
  rw [theta_cellAngles]
  rfl

theorem radius284 (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 284)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius<r := by
  have h := Leaf284TreeBridge.leaf284_tree_radius_gt y hy0 hy1 hc C Z r
    (by rw [anchors_identity]; exact hf)
  exact Terminal562Oracle.sourceRadius_lt_T.trans h
theorem radius562 (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 562)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius<r :=
  Terminal562Oracle.sourceRadius_lt_feasible y hy0 hc C Z r
    (by rw [anchors_identity]; exact hf)
theorem radius4348 (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4348)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius<r := by
  have h := Leaf4348TreeBridge.leaf4348_tree_radius_gt y hy0 hy1 hc C Z r
    (by rw [anchors_identity]; exact hf)
  have ht : (Leaf4348LP.T : ℝ)=(FlashCosineLeaf284Bridge.T : ℝ) := rfl
  rw [ht] at h
  exact Terminal562Oracle.sourceRadius_lt_T.trans h

def paidEnergyIDs : Finset (Fin 5011) := {284,562,4348}
theorem energy_count : paidEnergyIDs.card=3 := by decide +kernel
theorem energy_not_sharp : Disjoint paidEnergyIDs Patch120SharpDispatch.sharpIDs := by
  decide +kernel

/-- Exactly the three accepted energy consumers; no branch label substitutes
for a real lower bound. Cell y is closed and y may have zero coordinates. -/
theorem paid_energy_radius (n : Fin 5011) (hn : n∈paidEnergyIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius<r := by
  have h : n=284 ∨ n=562 ∨ n=4348 := by simpa only [paidEnergyIDs,Finset.mem_insert,
    Finset.mem_singleton] using hn
  rcases h with rfl | rfl | rfl
  · exact radius284 y hy0 hy1 hc C Z r hf
  · exact radius562 y hy0 hc C Z r hf
  · exact radius4348 y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyCommonChart
#check @N11Formalization.EnergyCommonChart.anchors_identity
#check @N11Formalization.EnergyCommonChart.paid_energy_radius
#print axioms N11Formalization.EnergyCommonChart.paid_energy_radius
