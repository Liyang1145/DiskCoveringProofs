import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapFourFieldCorrectedRowCaps
import N11Formalization.PaidCellCertificateMCap

/-! Conditional exclusions from the three corrected four-field witnesses. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldCorrectedTree
open ConvexMinorantCore DBMMinorantDual
noncomputable section

theorem db_eq_tree_1409 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (1409 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapFourFieldCorrectedRowCaps.db_1409 i j := by
  decide +kernel

theorem db_eq_tree_2337 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2337 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapFourFieldCorrectedRowCaps.db_2337 i j := by
  decide +kernel

theorem db_eq_tree_2341 : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data (2341 : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapFourFieldCorrectedRowCaps.db_2341 i j := by
  decide +kernel

theorem excluded_1409_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (1409 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_1409)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_1409 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_1409 FrozenCapRationalCore.G_1409
    FrozenCapFourFieldWitnessesCorrected.y4_1409 hf0 hg
    FrozenCapFourFieldWitnessesCorrected.nonneg_1409
    FrozenCapFourFieldWitnessesCorrected.sum_1409
  · intro a
    have hrow := FrozenCapFourFieldCorrectedRowCaps.row_cap_1409
      (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_1409 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapFourFieldCorrectedRowCaps.rowA,
      FrozenCapFourFieldWitnessesCorrected.y4_1409] using hrow
  · simpa only [FrozenCapRationalCore.T,
      N11Formalization.FlashCosineLeaf284Bridge.T] using
      FrozenCapFourFieldWitnessesCorrected.strict_gain_1409

theorem excluded_2337_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2337 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2337)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2337 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2337 FrozenCapRationalCore.G_2337
    FrozenCapFourFieldWitnessesCorrected.y4_2337 hf0 hg
    FrozenCapFourFieldWitnessesCorrected.nonneg_2337
    FrozenCapFourFieldWitnessesCorrected.sum_2337
  · intro a
    have hrow := FrozenCapFourFieldCorrectedRowCaps.row_cap_2337
      (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2337 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapFourFieldCorrectedRowCaps.rowA,
      FrozenCapFourFieldWitnessesCorrected.y4_2337] using hrow
  · simpa only [FrozenCapRationalCore.T,
      N11Formalization.FlashCosineLeaf284Bridge.T] using
      FrozenCapFourFieldWitnessesCorrected.strict_gain_2337

theorem excluded_2341_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2341 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2341)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2341 q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_2341 FrozenCapRationalCore.G_2341
    FrozenCapFourFieldWitnessesCorrected.y4_2341 hf0 hg
    FrozenCapFourFieldWitnessesCorrected.nonneg_2341
    FrozenCapFourFieldWitnessesCorrected.sum_2341
  · intro a
    have hrow := FrozenCapFourFieldCorrectedRowCaps.row_cap_2341
      (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_2341 (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapFourFieldCorrectedRowCaps.rowA,
      FrozenCapFourFieldWitnessesCorrected.y4_2341] using hrow
  · simpa only [FrozenCapRationalCore.T,
      N11Formalization.FlashCosineLeaf284Bridge.T] using
      FrozenCapFourFieldWitnessesCorrected.strict_gain_2341

end
end N11Formalization.FrozenCapFourFieldCorrectedTree

#check @N11Formalization.FrozenCapFourFieldCorrectedTree.excluded_1409_tree
#check @N11Formalization.FrozenCapFourFieldCorrectedTree.excluded_2341_tree
