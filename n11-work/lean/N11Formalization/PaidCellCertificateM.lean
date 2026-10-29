import N11Formalization.RoundedPaid16
import N11Formalization.CosineLinePacket
import N11Formalization.DBMAngleProvider
import N11Formalization.Paid16CellCertificate

/-! Row-count-generic version of `Paid16CellCertificate`. The field mixture is
still the explicit genuine16 packet; only the number `m` of nonnegative DBM
dual rows varies. This removes the hard-coded `Fin 7` limitation without
changing the numeric or geometric obligations. -/
set_option autoImplicit false
namespace N11Formalization.PaidCellCertificateM
open Finset FlashCosine
open FlashCosineLeaf284Bridge (iOf jOf)
open ConvexMinorantCore DBMMinorantDual
noncomputable section

structure Packet (m : ℕ) where
  nodeID : Fin 5011
  beta : Fin 16 → ℚ
  line : Fin 36 → CosineLinePacket.Packet
  rowFrom : Fin m → Fin 10
  rowTo : Fin m → Fin 10
  lam : Fin m → ℚ
  rmin : ℚ

def PA {m : ℕ} (p : Packet m) (k : Fin 36) : ℚ := (p.line k).a
def PB {m : ℕ} (p : Packet m) (k : Fin 36) : ℚ := (p.line k).b
def slopeQ {m : ℕ} (p : Packet m) (k : Fin 36) : ℚ := (p.line k).s
def interQ {m : ℕ} (p : Packet m) (k : Fin 36) : ℚ := (p.line k).c
def W {m : ℕ} (p : Packet m) (k : Fin 36) : ℚ := RoundedPaid16.mix p.beta k

structure Valid {m : ℕ} (p : Packet m) : Prop where
  beta_nonneg : ∀ f : Fin 16, 0 ≤ p.beta f
  beta_sum : (∑ f : Fin 16, p.beta f) = 1
  lines : ∀ k : Fin 36, CosineLinePacket.Valid (p.line k)
  endpoints : ∀ k : Fin 36,
    PA p k ≤ ((iOf k).val - (jOf k).val : ℚ) * LQ +
      Dq * DBMAngleProvider.slo p.nodeID k ∧
    ((iOf k).val - (jOf k).val : ℚ) * Lq +
      DQ * DBMAngleProvider.shi p.nodeID k ≤ PB p k
  lam_nonneg : ∀ a : Fin m, 0 ≤ p.lam a
  reduced : ∀ q : Fin 9, p.rmin ≤
    endpointLo Dq DQ (g (W p) (slopeQ p) q) + rho p.rowFrom p.rowTo p.lam q
  numeric : FlashCosineLeaf284Bridge.T ^ 2 <
    lower (W p) (slopeQ p) (interQ p) p.nodeID p.rowFrom p.rowTo p.lam p.rmin
  terminal : (DBMSourceTree.data p.nodeID).terminal = true

/-- The frozen seven-row packets are the `m = 7` instance of the generic API. -/
def of7 (p : Paid16CellCertificate.Packet) : Packet 7 where
  nodeID := p.nodeID
  beta := p.beta
  line := p.line
  rowFrom := p.rowFrom
  rowTo := p.rowTo
  lam := p.lam
  rmin := p.rmin

theorem of7_valid {p : Paid16CellCertificate.Packet}
    (hp : Paid16CellCertificate.Valid p) : Valid (of7 p) := by
  constructor
  · exact hp.beta_nonneg
  · exact hp.beta_sum
  · exact hp.lines
  · intro k
    simpa only [of7, PA, PB, Paid16CellCertificate.PA, Paid16CellCertificate.PB]
      using hp.endpoints k
  · exact hp.lam_nonneg
  · intro q
    change p.rmin ≤
      endpointLo Dq DQ (g (W (of7 p)) (slopeQ (of7 p)) q) +
        rho p.rowFrom p.rowTo p.lam q
    have hW : W (of7 p) = Paid16CellCertificate.W p := rfl
    have hs : slopeQ (of7 p) = Paid16CellCertificate.slopeQ p := rfl
    simpa only [hW, hs] using hp.reduced q
  · change FlashCosineLeaf284Bridge.T ^ 2 <
      lower (W (of7 p)) (slopeQ (of7 p)) (interQ (of7 p))
        p.nodeID p.rowFrom p.rowTo p.lam p.rmin
    have hW : W (of7 p) = Paid16CellCertificate.W p := rfl
    have hs : slopeQ (of7 p) = Paid16CellCertificate.slopeQ p := rfl
    have hi : interQ (of7 p) = Paid16CellCertificate.interQ p := rfl
    simpa only [hW, hs, hi] using hp.numeric
  · exact hp.terminal

theorem W_nonneg {m : ℕ} (p : Packet m) (hp : Valid p) (k : Fin 36) : 0 ≤ W p k :=
  RoundedPaid16.mix_nonneg p.beta hp.beta_nonneg k

theorem W_mix {m : ℕ} (p : Packet m) (hp : Valid p) (k : Fin 36) :
    W p k ≤ CertifiedFieldMixtures.mixWeight HarmonicFieldsPaid16.packet p.beta k :=
  RoundedPaid16.mix_le p.beta hp.beta_nonneg k

theorem pair_minorant {m : ℕ} (p : Packet m) (hp : Valid p) (k : Fin 36) :
    ∀ z ∈ Set.Icc (PA p k : ℝ) (PB p k : ℝ),
      (slopeQ p k : ℝ) * z + (interQ p k : ℝ) ≤ 1 - Real.cos z :=
  CosineLinePacket.minorant (p.line k) (hp.lines k)

theorem angles_in_cell {m : ℕ} (p : Packet m) (hp : Valid p)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 p.nodeID)
      (FlashLeafSplit.tlift y)) :
    ∀ k, zval y (iOf k) (jOf k) ∈ Set.Icc (PA p k : ℝ) (PB p k : ℝ) :=
  DBMAngleProvider.angles_of_endpoints p.nodeID (PA p) (PB p) hp.endpoints y hy0 hc

theorem oracle_gt {m : ℕ} (p : Packet m) (hp : Valid p)
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

theorem common_chart_radius {m : ℕ} (p : Packet m) (hp : Valid p)
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
end N11Formalization.PaidCellCertificateM
#check @N11Formalization.PaidCellCertificateM.oracle_gt
#check @N11Formalization.PaidCellCertificateM.common_chart_radius
#print axioms N11Formalization.PaidCellCertificateM.oracle_gt
#print axioms N11Formalization.PaidCellCertificateM.common_chart_radius
