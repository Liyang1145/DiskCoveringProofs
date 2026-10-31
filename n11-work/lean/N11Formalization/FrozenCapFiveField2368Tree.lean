import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapFiveField2368
import N11Formalization.FrozenCapRowCapTreeBridges
import N11Formalization.PaidCellCertificateMCap

/-! Conditional exclusion for node 2368 from the explicit five-field witness.
The packet `f0Lo`/`g` identifications remain hypotheses; no packet existence or
residual payment is claimed. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveField2368Tree
open N11Formalization.ConvexMinorantCore DBMMinorantDual
noncomputable section

theorem excluded_2368_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2368 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2368)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2368 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2368 FrozenCapRationalCore.G_2368
    FrozenCapFiveField2368.y5_2368 hf0 hg
    FrozenCapFiveField2368.nonneg_2368
    FrozenCapFiveField2368.sum_2368
  · intro a
    have hrow := FrozenCapFiveField2368.row_cap_2368 (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2368
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2368.rowA,
      FrozenCapFiveField2368.y5_2368] using hrow
  · simpa only [FrozenCapRationalCore.T,
      N11Formalization.FlashCosineLeaf284Bridge.T] using
      FrozenCapFiveField2368.strict_gain_2368

end
end N11Formalization.FrozenCapFiveField2368Tree

#check @N11Formalization.FrozenCapFiveField2368Tree.excluded_2368_tree
#print axioms N11Formalization.FrozenCapFiveField2368Tree.excluded_2368_tree
