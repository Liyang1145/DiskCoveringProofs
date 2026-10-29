import N11Formalization.PaidCellCertificateM

/-! Exact dual-weight transport for the general-row energy packets.

A nonnegative weight vector on the nine simplex coordinates turns ANY family
of nonnegative DBM rows into one cap inequality per ordered pair.  If the
weighted lower-endpoint gain plus `f0Lo` is below `T^2`, then no packet with
exactly the same frozen `f0Lo` and `g` can satisfy `Valid`, regardless of how
many rows it uses.  This is the proof-side counterpart of
`ops/lanes/C/certify_next512_row_cap.py`. -/
set_option autoImplicit false
namespace N11Formalization.PaidCellCertificateMCap
open Finset FlashCosine
open ConvexMinorantCore DBMMinorantDual
noncomputable section

/-- Weighted reduced-cost rows are dominated by the row-cap vector. -/
theorem weighted_reduced_le {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (y : Fin 9 → ℚ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : (∑ q : Fin 9, y q) = 1)
    (hcap : ∀ a : Fin m,
      (∑ q : Fin 9, y q * rowA (p.rowFrom a) (p.rowTo a) q) ≤
        db p.nodeID (p.rowFrom a) (p.rowTo a)) :
    p.rmin ≤ (∑ q : Fin 9, y q *
      endpointLo Dq DQ (g (PaidCellCertificateM.W p)
        (PaidCellCertificateM.slopeQ p) q)) +
      lamB p.nodeID p.rowFrom p.rowTo p.lam := by
  have hsum : (∑ q : Fin 9, y q * p.rmin) ≤
      ∑ q : Fin 9, y q *
        (endpointLo Dq DQ (g (PaidCellCertificateM.W p)
          (PaidCellCertificateM.slopeQ p) q) +
          rho p.rowFrom p.rowTo p.lam q) := by
    apply Finset.sum_le_sum
    intro q _
    exact mul_le_mul_of_nonneg_left (hp.reduced q) (hy0 q)
  have hrho : (∑ q : Fin 9,
        y q * rho p.rowFrom p.rowTo p.lam q) =
      ∑ a : Fin m, p.lam a *
        ∑ q : Fin 9, y q * rowA (p.rowFrom a) (p.rowTo a) q := by
    calc
      (∑ q : Fin 9, y q * rho p.rowFrom p.rowTo p.lam q)
          = ∑ q : Fin 9, ∑ a : Fin m,
              y q * (p.lam a * rowA (p.rowFrom a) (p.rowTo a) q) := by
            simp only [rho, Finset.mul_sum]
      _ = ∑ a : Fin m, ∑ q : Fin 9,
              y q * (p.lam a * rowA (p.rowFrom a) (p.rowTo a) q) :=
            Finset.sum_comm
      _ = ∑ a : Fin m, p.lam a *
              ∑ q : Fin 9, y q * rowA (p.rowFrom a) (p.rowTo a) q := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
  have hlam : (∑ a : Fin m, p.lam a *
        ∑ q : Fin 9, y q * rowA (p.rowFrom a) (p.rowTo a) q) ≤
      lamB p.nodeID p.rowFrom p.rowTo p.lam := by
    unfold lamB
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul_of_nonneg_left (hcap a) (hp.lam_nonneg a)
  calc
    p.rmin = ∑ q : Fin 9, y q * p.rmin := by
      rw [← Finset.sum_mul, hy1, one_mul]
    _ ≤ ∑ q : Fin 9, y q *
        (endpointLo Dq DQ (g (PaidCellCertificateM.W p)
          (PaidCellCertificateM.slopeQ p) q) +
          rho p.rowFrom p.rowTo p.lam q) := hsum
    _ = (∑ q : Fin 9, y q *
          endpointLo Dq DQ (g (PaidCellCertificateM.W p)
            (PaidCellCertificateM.slopeQ p) q)) +
        ∑ q : Fin 9, y q * rho p.rowFrom p.rowTo p.lam q := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ (∑ q : Fin 9, y q *
          endpointLo Dq DQ (g (PaidCellCertificateM.W p)
            (PaidCellCertificateM.slopeQ p) q)) +
        lamB p.nodeID p.rowFrom p.rowTo p.lam := by
      exact add_le_add_left (hrho.trans_le hlam) _

/-- The cap certificate contradicts the packet's strict numeric check. -/
theorem not_valid_of_weighted_gain {m : ℕ}
    (p : PaidCellCertificateM.Packet m) (hp : PaidCellCertificateM.Valid p)
    (y : Fin 9 → ℚ) (hy0 : ∀ q, 0 ≤ y q)
    (hy1 : (∑ q : Fin 9, y q) = 1)
    (hcap : ∀ a : Fin m,
      (∑ q : Fin 9, y q * rowA (p.rowFrom a) (p.rowTo a) q) ≤
        db p.nodeID (p.rowFrom a) (p.rowTo a))
    (hgain : f0Lo (PaidCellCertificateM.W p)
        (PaidCellCertificateM.slopeQ p) (PaidCellCertificateM.interQ p) +
      ∑ q : Fin 9, y q * endpointLo Dq DQ
        (g (PaidCellCertificateM.W p)
          (PaidCellCertificateM.slopeQ p) q) <
      FlashCosineLeaf284Bridge.T ^ 2) : False := by
  have hlow := weighted_reduced_le p hp y hy0 hy1 hcap
  have hle : lower (PaidCellCertificateM.W p)
      (PaidCellCertificateM.slopeQ p) (PaidCellCertificateM.interQ p)
      p.nodeID p.rowFrom p.rowTo p.lam p.rmin ≤
      f0Lo (PaidCellCertificateM.W p)
        (PaidCellCertificateM.slopeQ p) (PaidCellCertificateM.interQ p) +
      ∑ q : Fin 9, y q * endpointLo Dq DQ
        (g (PaidCellCertificateM.W p)
          (PaidCellCertificateM.slopeQ p) q) := by
    unfold lower
    linarith
  linarith [hp.numeric]

/-- Frozen-proposal form used by emitted seven-node exclusion modules. -/
theorem not_valid_of_frozen_cap {m : ℕ}
    (p : PaidCellCertificateM.Packet m) (hp : PaidCellCertificateM.Valid p)
    (F0 : ℚ) (G : Fin 9 → ℚ) (y : Fin 9 → ℚ)
    (hf0 : f0Lo (PaidCellCertificateM.W p)
      (PaidCellCertificateM.slopeQ p) (PaidCellCertificateM.interQ p) = F0)
    (hg : ∀ q, g (PaidCellCertificateM.W p)
      (PaidCellCertificateM.slopeQ p) q = G q)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : (∑ q : Fin 9, y q) = 1)
    (hcap : ∀ a : Fin m,
      (∑ q : Fin 9, y q * rowA (p.rowFrom a) (p.rowTo a) q) ≤
        db p.nodeID (p.rowFrom a) (p.rowTo a))
    (hgain : F0 + ∑ q : Fin 9, y q * endpointLo Dq DQ (G q) <
      FlashCosineLeaf284Bridge.T ^ 2) : False := by
  apply not_valid_of_weighted_gain p hp y hy0 hy1 hcap
  simpa only [hf0, hg] using hgain

end
end N11Formalization.PaidCellCertificateMCap
#check @N11Formalization.PaidCellCertificateMCap.weighted_reduced_le
#check @N11Formalization.PaidCellCertificateMCap.not_valid_of_weighted_gain
#check @N11Formalization.PaidCellCertificateMCap.not_valid_of_frozen_cap
#print axioms N11Formalization.PaidCellCertificateMCap.weighted_reduced_le
#print axioms N11Formalization.PaidCellCertificateMCap.not_valid_of_weighted_gain
#print axioms N11Formalization.PaidCellCertificateMCap.not_valid_of_frozen_cap
