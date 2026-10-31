import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapFiveField2370
import N11Formalization.FrozenCapRowCapTreeBridges
import N11Formalization.PaidCellCertificateMCap

/-! Conditional exclusion for node 2370 from the explicit five-field witness.
The packet `f0Lo`/`g` identifications remain hypotheses; no packet existence or
residual payment is claimed. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveField2370Tree
open N11Formalization.ConvexMinorantCore DBMMinorantDual
noncomputable section

theorem excluded_2370_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2370 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2370)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2370 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2370 FrozenCapRationalCore.G_2370
    FrozenCapFiveField2370.y5_2370 hf0 hg
    FrozenCapFiveField2370.nonneg_2370
    FrozenCapFiveField2370.sum_2370
  · intro a
    have hrow := FrozenCapFiveField2370.row_cap_2370 (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2370
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2370.rowA,
      FrozenCapFiveField2370.y5_2370] using hrow
  · simpa only [FrozenCapRationalCore.T,
      N11Formalization.FlashCosineLeaf284Bridge.T] using
      FrozenCapFiveField2370.strict_gain_2370

end
end N11Formalization.FrozenCapFiveField2370Tree

#check @N11Formalization.FrozenCapFiveField2370Tree.excluded_2370_tree
#print axioms N11Formalization.FrozenCapFiveField2370Tree.excluded_2370_tree
