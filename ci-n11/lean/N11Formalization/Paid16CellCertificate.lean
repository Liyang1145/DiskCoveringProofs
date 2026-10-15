import N11Formalization.RoundedPaid16
import N11Formalization.CosineLinePacket
import N11Formalization.DBMAngleProvider

/-! Reusable genuine16-field OWN-cell certificate. Valid remains EXPLICIT
until a concrete packet is kernel-paid. No recorded energy or solver input. -/
set_option autoImplicit false
namespace N11Formalization.Paid16CellCertificate
open Finset FlashCosine
open FlashCosineLeaf284Bridge (iOf jOf)
open ConvexMinorantCore DBMMinorantDual
noncomputable section

structure Packet where
  nodeID : Fin 5011
  beta : Fin 16 → ℚ
  line : Fin 36 → CosineLinePacket.Packet
  rowFrom : Fin 7 → Fin 10
  rowTo : Fin 7 → Fin 10
  lam : Fin 7 → ℚ
  rmin : ℚ

def PA (p : Packet) (k : Fin 36) : ℚ := (p.line k).a
def PB (p : Packet) (k : Fin 36) : ℚ := (p.line k).b
def slopeQ (p : Packet) (k : Fin 36) : ℚ := (p.line k).s
def interQ (p : Packet) (k : Fin 36) : ℚ := (p.line k).c
def W (p : Packet) (k : Fin 36) : ℚ := RoundedPaid16.mix p.beta k

structure Valid (p : Packet) : Prop where
  beta_nonneg : ∀ f : Fin 16, 0 ≤ p.beta f
  beta_sum : (∑ f : Fin 16, p.beta f) = 1
  lines : ∀ k : Fin 36, CosineLinePacket.Valid (p.line k)
  endpoints : ∀ k : Fin 36,
    PA p k ≤ ((iOf k).val - (jOf k).val : ℚ) * LQ +
      Dq * DBMAngleProvider.slo p.nodeID k ∧
    ((iOf k).val - (jOf k).val : ℚ) * Lq +
      DQ * DBMAngleProvider.shi p.nodeID k ≤ PB p k
  lam_nonneg : ∀ a : Fin 7, 0 ≤ p.lam a
  reduced : ∀ q : Fin 9, p.rmin ≤
    endpointLo Dq DQ (g (W p) (slopeQ p) q) + rho p.rowFrom p.rowTo p.lam q
  numeric : FlashCosineLeaf284Bridge.T ^ 2 <
    lower (W p) (slopeQ p) (interQ p) p.nodeID p.rowFrom p.rowTo p.lam p.rmin
  terminal : (DBMSourceTree.data p.nodeID).terminal = true

theorem W_nonneg (p : Packet) (hp : Valid p) (k : Fin 36) : 0 ≤ W p k :=
  RoundedPaid16.mix_nonneg p.beta hp.beta_nonneg k
theorem W_mix (p : Packet) (hp : Valid p) (k : Fin 36) :
    W p k ≤ CertifiedFieldMixtures.mixWeight HarmonicFieldsPaid16.packet p.beta k :=
  RoundedPaid16.mix_le p.beta hp.beta_nonneg k
theorem pair_minorant (p : Packet) (hp : Valid p) (k : Fin 36) :
    ∀ z ∈ Set.Icc (PA p k : ℝ) (PB p k : ℝ),
      (slopeQ p k : ℝ) * z + (interQ p k : ℝ) ≤ 1 - Real.cos z :=
  CosineLinePacket.minorant (p.line k) (hp.lines k)
theorem angles_in_cell (p : Packet) (hp : Valid p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 p.nodeID)
      (FlashLeafSplit.tlift y)) :
    ∀ k, zval y (iOf k) (jOf k) ∈ Set.Icc (PA p k : ℝ) (PB p k : ℝ) :=
  DBMAngleProvider.angles_of_endpoints p.nodeID (PA p) (PB p) hp.endpoints y hy0 hc
theorem oracle_gt (p : Packet) (hp : Valid p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 p.nodeID)
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ) ^ 2 <
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) := by
  have hnum : (FlashCosineLeaf284Bridge.T : ℝ) ^ 2 <
      (lower (W p) (slopeQ p) (interQ p) p.nodeID p.rowFrom p.rowTo p.lam p.rmin : ℝ) := by
    exact_mod_cast hp.numeric
  have hlo := hnum.trans_le
    (affine_lower_of_dual (W p) (slopeQ p) (interQ p) p.nodeID
      p.rowFrom p.rowTo p.lam p.rmin hp.lam_nonneg hp.reduced y hy0 hy1 hc)
  exact hlo.trans_le
    (CertifiedFieldMixtures.affine_le_oracle HarmonicFieldsPaid16.packet
      HarmonicFieldsPaid16.all_valid p.beta (W p) (slopeQ p) (interQ p) (PA p) (PB p)
      hp.beta_nonneg hp.beta_sum (W_nonneg p hp) (W_mix p hp) (pair_minorant p hp)
      y (angles_in_cell p hp y hy0 hc))
theorem common_chart_radius (p : Packet) (hp : Valid p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 p.nodeID)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  CertifiedFieldMixtures.radius_of_dual HarmonicFieldsPaid16.packet
    HarmonicFieldsPaid16.all_valid p.beta (W p) (slopeQ p) (interQ p) (PA p) (PB p)
    p.nodeID p.rowFrom p.rowTo p.lam p.rmin hp.beta_nonneg hp.beta_sum
    (W_nonneg p hp) (W_mix p hp) (pair_minorant p hp) hp.lam_nonneg hp.reduced hp.numeric
    y hy0 hy1 hc (angles_in_cell p hp y hy0 hc) C Z r hf
end
end N11Formalization.Paid16CellCertificate
#check @N11Formalization.Paid16CellCertificate.oracle_gt
#check @N11Formalization.Paid16CellCertificate.common_chart_radius
#print axioms N11Formalization.Paid16CellCertificate.oracle_gt
#print axioms N11Formalization.Paid16CellCertificate.common_chart_radius
