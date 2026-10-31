import N11Formalization.FrozenCapPublicExcludedTree

/-! Dependency-clean wrappers for the two unpaid public five-field trees.

The wide-field public tree is already kernel-green. These aliases expose the
same conditional exclusions in the namespaces consumed by the five-field tree
modules, without changing the frozen five-field bytes and without claiming
packet existence or paying a residual radius. -/
set_option autoImplicit false
namespace N11Formalization.LaneBUnpaidPublicExcludedWrappers
open N11Formalization.ConvexMinorantCore DBMMinorantDual
noncomputable section

theorem excluded_2368
    {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2368 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2368)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2368 q) : False :=
  FrozenCapPublicExcludedTree.excluded_2368_tree p hp hnode hf0 hg

theorem excluded_2370
    {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2370 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2370)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2370 q) : False :=
  FrozenCapPublicExcludedTree.excluded_2370_tree p hp hnode hf0 hg

end
end N11Formalization.LaneBUnpaidPublicExcludedWrappers

namespace N11Formalization.FrozenCapFiveField2368Tree
open N11Formalization.ConvexMinorantCore DBMMinorantDual

theorem excluded_2368_tree
    {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2368 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2368)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2368 q) : False :=
  N11Formalization.LaneBUnpaidPublicExcludedWrappers.excluded_2368 p hp hnode hf0 hg

end N11Formalization.FrozenCapFiveField2368Tree

namespace N11Formalization.FrozenCapFiveField2370Tree
open N11Formalization.ConvexMinorantCore DBMMinorantDual

theorem excluded_2370_tree
    {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = (2370 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_2370)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_2370 q) : False :=
  N11Formalization.LaneBUnpaidPublicExcludedWrappers.excluded_2370 p hp hnode hf0 hg

end N11Formalization.FrozenCapFiveField2370Tree

#check @N11Formalization.LaneBUnpaidPublicExcludedWrappers.excluded_2368
#check @N11Formalization.LaneBUnpaidPublicExcludedWrappers.excluded_2370
#check @N11Formalization.FrozenCapFiveField2368Tree.excluded_2368_tree
#check @N11Formalization.FrozenCapFiveField2370Tree.excluded_2370_tree
#print axioms N11Formalization.LaneBUnpaidPublicExcludedWrappers.excluded_2368
#print axioms N11Formalization.LaneBUnpaidPublicExcludedWrappers.excluded_2370
#print axioms N11Formalization.FrozenCapFiveField2368Tree.excluded_2368_tree
#print axioms N11Formalization.FrozenCapFiveField2370Tree.excluded_2370_tree
