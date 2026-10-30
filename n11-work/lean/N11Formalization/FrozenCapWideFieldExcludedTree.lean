import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapWideFieldRowCaps
import N11Formalization.PaidCellCertificateMCap

/-! Node-pinned wrappers for the seven wide-support exclusions.  They remain
conditional on the packet's `f0Lo`/`g` identifications, which are not supplied. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapWideFieldExcludedTree
open Finset ConvexMinorantCore DBMMinorantDual
open FrozenCapRationalCore
open N11Formalization.FrozenCapWideFieldWitnesses
open N11Formalization.FrozenCapWideFieldRowCaps
noncomputable section

theorem db_eq_tree_1409 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (1409 : Fin 5011)).db i j : ℚ) / 4096) =
      db_1409 i j := by
  decide +kernel

theorem db_eq_tree_2337 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2337 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2337 i j := by
  decide +kernel

theorem db_eq_tree_2341 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2341 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2341 i j := by
  decide +kernel

theorem db_eq_tree_2356 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2356 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2356 i j := by
  decide +kernel

theorem db_eq_tree_2360 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2360 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2360 i j := by
  decide +kernel

theorem db_eq_tree_2368 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2368 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2368 i j := by
  decide +kernel

theorem db_eq_tree_2370 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2370 : Fin 5011)).db i j : ℚ) / 4096) =
      db_2370 i j := by
  decide +kernel

theorem excluded_1409_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (1409 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_1409)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q = G_1409 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_1409 G_1409 yW_1409
    hf0 hg nonneg_1409 sum_1409
  · intro a
    have hrow := row_cap_1409 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_1409 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only [T, N11Formalization.FlashCosineLeaf284Bridge.T] using strict_gain_1409

theorem excluded_2337_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2337 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2337)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q = G_2337 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2337 G_2337 yW_2337
    hf0 hg nonneg_2337 sum_2337
  · intro a
    have hrow := row_cap_2337 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2337 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only [T, N11Formalization.FlashCosineLeaf284Bridge.T] using strict_gain_2337

theorem excluded_2341_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2341 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2341)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q = G_2341 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2341 G_2341 yW_2341
    hf0 hg nonneg_2341 sum_2341
  · intro a
    have hrow := row_cap_2341 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2341 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only [T, N11Formalization.FlashCosineLeaf284Bridge.T] using strict_gain_2341

theorem excluded_2356_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2356 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2356)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q = G_2356 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2356 G_2356 yW_2356
    hf0 hg nonneg_2356 sum_2356
  · intro a
    have hrow := row_cap_2356 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2356 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only [T, N11Formalization.FlashCosineLeaf284Bridge.T] using strict_gain_2356

theorem excluded_2360_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2360 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2360)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q = G_2360 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2360 G_2360 yW_2360
    hf0 hg nonneg_2360 sum_2360
  · intro a
    have hrow := row_cap_2360 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2360 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only [T, N11Formalization.FlashCosineLeaf284Bridge.T] using strict_gain_2360

theorem excluded_2368_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2368 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2368)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q = G_2368 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2368 G_2368 yW_2368
    hf0 hg nonneg_2368 sum_2368
  · intro a
    have hrow := row_cap_2368 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2368 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only [T, N11Formalization.FlashCosineLeaf284Bridge.T] using strict_gain_2368

theorem excluded_2370_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2370 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = F0_2370)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q = G_2370 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp F0_2370 G_2370 yW_2370
    hf0 hg nonneg_2370 sum_2370
  · intro a
    have hrow := row_cap_2370 (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2370 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, rowA] using hrow
  · simpa only [T, N11Formalization.FlashCosineLeaf284Bridge.T] using strict_gain_2370

end
end N11Formalization.FrozenCapWideFieldExcludedTree

#check @N11Formalization.FrozenCapWideFieldExcludedTree.excluded_1409_tree
#check @N11Formalization.FrozenCapWideFieldExcludedTree.excluded_2370_tree
