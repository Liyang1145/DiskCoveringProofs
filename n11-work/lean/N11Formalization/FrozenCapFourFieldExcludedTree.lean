import N11Formalization.FrozenCapFourFieldRowCaps
import N11Formalization.FrozenCapRowCapTreeBridges

/-! Node-pinned exclusion wrappers for the five corrected four-field mixtures.

The wrappers remain conditional on the packet's `f0Lo` and `g` identification
hypotheses; those are not supplied here. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldExcludedTree
open Finset ConvexMinorantCore DBMMinorantDual
open FrozenCapRationalCore
open N11Formalization.FrozenCapFourFieldWitnesses
open N11Formalization.FrozenCapFourFieldRowCaps
noncomputable section

theorem excluded_1409_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (1409 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_1409)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      G_1409 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_1409 G_1409 y4_1409
    hf0 hg nonneg_1409 sum_1409
  · intro a
    have hrow := row_cap_1409 (p.rowFrom a) (p.rowTo a)
    have hbridge := N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_1409
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only using strict_gain_1409

theorem excluded_2337_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2337 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2337)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      G_2337 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2337 G_2337 y4_2337
    hf0 hg nonneg_2337 sum_2337
  · intro a
    have hrow := row_cap_2337 (p.rowFrom a) (p.rowTo a)
    have hbridge := N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_2337
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only using strict_gain_2337

theorem excluded_2341_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2341 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2341)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      G_2341 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2341 G_2341 y4_2341
    hf0 hg nonneg_2341 sum_2341
  · intro a
    have hrow := row_cap_2341 (p.rowFrom a) (p.rowTo a)
    have hbridge := N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_2341
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only using strict_gain_2341

theorem excluded_2368_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2368 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2368)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      G_2368 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2368 G_2368 y4_2368
    hf0 hg nonneg_2368 sum_2368
  · intro a
    have hrow := row_cap_2368 (p.rowFrom a) (p.rowTo a)
    have hbridge := N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_2368
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only using strict_gain_2368

theorem excluded_2370_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2370 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2370)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      G_2370 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2370 G_2370 y4_2370
    hf0 hg nonneg_2370 sum_2370
  · intro a
    have hrow := row_cap_2370 (p.rowFrom a) (p.rowTo a)
    have hbridge := N11Formalization.FrozenCapRowCapTreeBridges.db_eq_tree_2370
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only using strict_gain_2370

end
end N11Formalization.FrozenCapFourFieldExcludedTree

#check @N11Formalization.FrozenCapFourFieldExcludedTree.excluded_1409_tree
#check @N11Formalization.FrozenCapFourFieldExcludedTree.excluded_2370_tree
#print axioms N11Formalization.FrozenCapFourFieldExcludedTree.excluded_1409_tree
#print axioms N11Formalization.FrozenCapFourFieldExcludedTree.excluded_2370_tree
