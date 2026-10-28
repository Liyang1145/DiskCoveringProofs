import N11Formalization
set_option autoImplicit false
open N11Formalization Finset FlashCosine
open Paid16CellCertificate
open FlashCosineLeaf284Bridge (iOf jOf)
set_option maxRecDepth 10000
namespace GeneralFirst42Controls
def good : Packet := Paid16GeneralG01.packet 0
theorem good_valid : Valid good := Paid16GeneralG01.all_valid 0
def zeroBeta : Packet := {good with beta := fun _ => 0}
def betaTwo : Packet := {good with beta := fun f => good.beta f + (if f = 0 then 1 else 0)}
def negativeLam : Packet := {good with lam := fun a => if a = 0 then -1 else good.lam a}
def badShift : Packet := {good with line :=
  fun k => if k = 0 then {good.line k with shift := 97} else good.line k}
def wrongNode : Packet := {good with nodeID := 3}
def zeroDual : Packet := {good with lam := fun _ => 0}
theorem zero_beta_rejected : ¬Valid zeroBeta := by
  intro h
  have hs := h.beta_sum
  change (∑ _f : Fin 16, (0 : ℚ)) = 1 at hs
  norm_num at hs
theorem beta_two_rejected : ¬Valid betaTwo := by
  intro h
  have hs := h.beta_sum
  have hbad : (∑ f : Fin 16, betaTwo.beta f) ≠ 1 := by decide +kernel
  exact hbad hs
theorem negative_lam_rejected : ¬Valid negativeLam := by
  intro h
  have hn := h.lam_nonneg 0
  change (0 : ℚ) ≤ -1 at hn
  norm_num at hn
theorem shift_rejected : ¬Valid badShift := by
  intro h
  have hn := h.lines 0
  have hbad : ¬CosineLinePacket.Valid (badShift.line 0) := by decide +kernel
  exact hbad hn
theorem wrong_cell_rejected : ¬Valid wrongNode := by
  intro h
  have hn := h.endpoints 0
  have hbad : ¬(PA wrongNode 0 ≤
      ((FlashCosineLeaf284Bridge.iOf 0).val-(FlashCosineLeaf284Bridge.jOf 0).val : ℚ)*LQ +
      Dq*DBMAngleProvider.slo wrongNode.nodeID 0 ∧
    ((FlashCosineLeaf284Bridge.iOf 0).val-(FlashCosineLeaf284Bridge.jOf 0).val : ℚ)*Lq+
      DQ*DBMAngleProvider.shi wrongNode.nodeID 0 ≤ PB wrongNode 0) := by decide +kernel
  exact hbad hn
theorem zero_dual_rejected : ¬Valid zeroDual := by
  intro h
  have hn := h.reduced
  have hbad : ¬(∀ q : Fin 9, zeroDual.rmin ≤
      ConvexMinorantCore.endpointLo Dq DQ (ConvexMinorantCore.g (W zeroDual) (slopeQ zeroDual) q) +
        DBMMinorantDual.rho zeroDual.rowFrom zeroDual.rowTo zeroDual.lam q) := by decide +kernel
  exact hbad hn
end GeneralFirst42Controls
#print axioms GeneralFirst42Controls.good_valid
#print axioms GeneralFirst42Controls.zero_beta_rejected
#print axioms GeneralFirst42Controls.beta_two_rejected
#print axioms GeneralFirst42Controls.negative_lam_rejected
#print axioms GeneralFirst42Controls.shift_rejected
#print axioms GeneralFirst42Controls.wrong_cell_rejected
#print axioms GeneralFirst42Controls.zero_dual_rejected
