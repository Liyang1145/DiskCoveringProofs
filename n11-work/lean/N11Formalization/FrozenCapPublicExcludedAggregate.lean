import N11Formalization.FrozenCapPublicExcludedTree

/-! One consumer interface for the seven public frozen-cap tree exclusions.

The hypotheses remain the exact packet `f0Lo`/`g` identifications.  This
module only removes repeated seven-way dispatch at call sites; it does not
claim packet existence or pay a residual id. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapPublicExcludedAggregate
open ConvexMinorantCore DBMMinorantDual
noncomputable section

def PublicResidualData {m : ℕ} (p : PaidCellCertificateM.Packet m) : Prop :=
  (p.nodeID = (1409 : Fin 5011) ∧
    f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_1409 ∧
    (∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_1409 q)) ∨
  (p.nodeID = (2337 : Fin 5011) ∧
    f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2337 ∧
    (∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2337 q)) ∨
  (p.nodeID = (2341 : Fin 5011) ∧
    f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2341 ∧
    (∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2341 q)) ∨
  (p.nodeID = (2356 : Fin 5011) ∧
    f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2356 ∧
    (∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2356 q)) ∨
  (p.nodeID = (2360 : Fin 5011) ∧
    f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2360 ∧
    (∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2360 q)) ∨
  (p.nodeID = (2368 : Fin 5011) ∧
    f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2368 ∧
    (∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2368 q)) ∨
  (p.nodeID = (2370 : Fin 5011) ∧
    f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2370 ∧
    (∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2370 q))

theorem not_valid_of_public_residual {m : ℕ}
    (p : PaidCellCertificateM.Packet m) (hp : PaidCellCertificateM.Valid p)
    (h : PublicResidualData p) : False := by
  rcases h with ⟨hnode, hf0, hg⟩ | ⟨hnode, hf0, hg⟩ |
    ⟨hnode, hf0, hg⟩ | ⟨hnode, hf0, hg⟩ | ⟨hnode, hf0, hg⟩ |
    ⟨hnode, hf0, hg⟩ | ⟨hnode, hf0, hg⟩
  · exact FrozenCapPublicExcludedTree.excluded_1409_tree p hp hnode hf0 hg
  · exact FrozenCapPublicExcludedTree.excluded_2337_tree p hp hnode hf0 hg
  · exact FrozenCapPublicExcludedTree.excluded_2341_tree p hp hnode hf0 hg
  · exact FrozenCapPublicExcludedTree.excluded_2356_tree p hp hnode hf0 hg
  · exact FrozenCapPublicExcludedTree.excluded_2360_tree p hp hnode hf0 hg
  · exact FrozenCapPublicExcludedTree.excluded_2368_tree p hp hnode hf0 hg
  · exact FrozenCapPublicExcludedTree.excluded_2370_tree p hp hnode hf0 hg

end
end N11Formalization.FrozenCapPublicExcludedAggregate

#check @N11Formalization.FrozenCapPublicExcludedAggregate.not_valid_of_public_residual
#print axioms N11Formalization.FrozenCapPublicExcludedAggregate.not_valid_of_public_residual
