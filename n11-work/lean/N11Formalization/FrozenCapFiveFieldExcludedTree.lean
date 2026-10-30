import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapFiveFieldRowCaps

/-! Node-pinned exclusion wrappers for the five-field rescues at 2356 and 2360.

The wrappers still require the packet's `f0Lo` and `g` identification hypotheses;
those are not supplied here. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveFieldExcludedTree
open Finset ConvexMinorantCore DBMMinorantDual
open N11Formalization.FrozenCapFiveFieldWitnesses
open N11Formalization.FrozenCapFiveFieldRowCaps
noncomputable section

theorem db_eq_tree_2356 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2356 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2356 i j := by
  decide +kernel

theorem db_eq_tree_2360 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2360 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2360 i j := by
  decide +kernel

theorem excluded_2356_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2356 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2356)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      G_2356 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2356 G_2356 y5_2356
    hf0 hg nonneg_2356 sum_2356
  · intro a
    have hrow := row_cap_2356 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2356 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only using strict_gain_2356

theorem excluded_2360_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2360 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2360)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      G_2360 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2360 G_2360 y5_2360
    hf0 hg nonneg_2360 sum_2360
  · intro a
    have hrow := row_cap_2360 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2360 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only using strict_gain_2360

end
end N11Formalization.FrozenCapFiveFieldExcludedTree

#check @N11Formalization.FrozenCapFiveFieldExcludedTree.excluded_2356_tree
#check @N11Formalization.FrozenCapFiveFieldExcludedTree.excluded_2360_tree
#print axioms N11Formalization.FrozenCapFiveFieldExcludedTree.excluded_2356_tree
#print axioms N11Formalization.FrozenCapFiveFieldExcludedTree.excluded_2360_tree
