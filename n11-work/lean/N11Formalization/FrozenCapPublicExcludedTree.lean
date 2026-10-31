import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapRowCapTreeBridges
import N11Formalization.FrozenCapWideFieldWitnesses
import N11Formalization.PaidCellCertificateMCap

/-! Node-pinned wide-support exclusions for the seven public residual ids.

This is the dependency-clean counterpart of
`FrozenCapWideFieldExcludedTree`: it uses the seven small per-node row-cap
certificates and their source-tree bridges instead of the red bulk
`FrozenCapWideFieldRowCaps` module.  The results remain conditional on the
packet's `f0Lo` and `g` identifications and do not pay any residual id. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapPublicExcludedTree
open Finset ConvexMinorantCore DBMMinorantDual
noncomputable section

theorem core_Dq_eq_flash : FrozenCapRationalCore.Dq = FlashCosine.Dq := rfl
theorem core_DQ_eq_flash : FrozenCapRationalCore.DQ = FlashCosine.DQ := rfl
theorem core_T_eq_flash : FrozenCapRationalCore.T = FlashCosineLeaf284Bridge.T := rfl

theorem strict_gain_to_flash {F0 : ℚ} {G : Fin 9 → ℚ} (y : Fin 9 → ℚ)
    (h : F0 + ∑ q, y q * endpointLo FrozenCapRationalCore.Dq
      FrozenCapRationalCore.DQ (G q) < FrozenCapRationalCore.T ^ 2) :
    F0 + ∑ q, y q * endpointLo FlashCosine.Dq FlashCosine.DQ (G q) <
      FlashCosineLeaf284Bridge.T ^ 2 := by
  rw [← core_Dq_eq_flash, ← core_DQ_eq_flash, ← core_T_eq_flash]
  exact h

theorem excluded_1409_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (1409 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_1409)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_1409 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_1409 FrozenCapRationalCore.G_1409
    FrozenCapWideFieldWitnesses.yW_1409 hf0 hg
    FrozenCapWideFieldWitnesses.nonneg_1409
    FrozenCapWideFieldWitnesses.sum_1409
  · intro a
    have hrow := FrozenCapRowCap1409.row_cap (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_1409
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap1409.rowA,
      FrozenCapWideFieldWitnesses.yW_1409] using hrow
  · exact strict_gain_to_flash _ FrozenCapWideFieldWitnesses.strict_gain_1409

theorem excluded_2337_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2337 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2337)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2337 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2337 FrozenCapRationalCore.G_2337
    FrozenCapWideFieldWitnesses.yW_2337 hf0 hg
    FrozenCapWideFieldWitnesses.nonneg_2337
    FrozenCapWideFieldWitnesses.sum_2337
  · intro a
    have hrow := FrozenCapRowCap2337.row_cap (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2337
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2337.rowA,
      FrozenCapWideFieldWitnesses.yW_2337] using hrow
  · exact strict_gain_to_flash _ FrozenCapWideFieldWitnesses.strict_gain_2337

theorem excluded_2341_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2341 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2341)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2341 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2341 FrozenCapRationalCore.G_2341
    FrozenCapWideFieldWitnesses.yW_2341 hf0 hg
    FrozenCapWideFieldWitnesses.nonneg_2341
    FrozenCapWideFieldWitnesses.sum_2341
  · intro a
    have hrow := FrozenCapRowCap2341.row_cap (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2341
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2341.rowA,
      FrozenCapWideFieldWitnesses.yW_2341] using hrow
  · exact strict_gain_to_flash _ FrozenCapWideFieldWitnesses.strict_gain_2341

theorem excluded_2356_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2356 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2356)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2356 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2356 FrozenCapRationalCore.G_2356
    FrozenCapWideFieldWitnesses.yW_2356 hf0 hg
    FrozenCapWideFieldWitnesses.nonneg_2356
    FrozenCapWideFieldWitnesses.sum_2356
  · intro a
    have hrow := FrozenCapRowCap2356.row_cap (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2356
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2356.rowA,
      FrozenCapWideFieldWitnesses.yW_2356] using hrow
  · exact strict_gain_to_flash _ FrozenCapWideFieldWitnesses.strict_gain_2356

theorem excluded_2360_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2360 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2360)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2360 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2360 FrozenCapRationalCore.G_2360
    FrozenCapWideFieldWitnesses.yW_2360 hf0 hg
    FrozenCapWideFieldWitnesses.nonneg_2360
    FrozenCapWideFieldWitnesses.sum_2360
  · intro a
    have hrow := FrozenCapRowCap2360.row_cap (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2360
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2360.rowA,
      FrozenCapWideFieldWitnesses.yW_2360] using hrow
  · exact strict_gain_to_flash _ FrozenCapWideFieldWitnesses.strict_gain_2360

theorem excluded_2368_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2368 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2368)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2368 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2368 FrozenCapRationalCore.G_2368
    FrozenCapWideFieldWitnesses.yW_2368 hf0 hg
    FrozenCapWideFieldWitnesses.nonneg_2368
    FrozenCapWideFieldWitnesses.sum_2368
  · intro a
    have hrow := FrozenCapRowCap2368.row_cap (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2368
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2368.rowA,
      FrozenCapWideFieldWitnesses.yW_2368] using hrow
  · exact strict_gain_to_flash _ FrozenCapWideFieldWitnesses.strict_gain_2368

theorem excluded_2370_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2370 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2370)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2370 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2370 FrozenCapRationalCore.G_2370
    FrozenCapWideFieldWitnesses.yW_2370 hf0 hg
    FrozenCapWideFieldWitnesses.nonneg_2370
    FrozenCapWideFieldWitnesses.sum_2370
  · intro a
    have hrow := FrozenCapRowCap2370.row_cap (p.rowFrom a) (p.rowTo a)
    have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2370
      (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapRowCap2370.rowA,
      FrozenCapWideFieldWitnesses.yW_2370] using hrow
  · exact strict_gain_to_flash _ FrozenCapWideFieldWitnesses.strict_gain_2370

end
end N11Formalization.FrozenCapPublicExcludedTree

#check @N11Formalization.FrozenCapPublicExcludedTree.excluded_1409_tree
#check @N11Formalization.FrozenCapPublicExcludedTree.excluded_2370_tree
#print axioms N11Formalization.FrozenCapPublicExcludedTree.excluded_1409_tree
#print axioms N11Formalization.FrozenCapPublicExcludedTree.excluded_2370_tree
