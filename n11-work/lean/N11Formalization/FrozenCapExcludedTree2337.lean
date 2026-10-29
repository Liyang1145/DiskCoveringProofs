import N11Formalization.FrozenCapCertificates
import N11Formalization.FrozenCapRowCap2337
import N11Formalization.FrozenCapRowCapTreeBridges

/-! Node-identity wrapper for the frozen-cap exclusion at public node 2337.

`FrozenCapCertificates.excluded_2337` is stated for an arbitrary packet node.
This module fixes `p.nodeID` to the frozen source node and derives the row-cap
hypothesis from the exact 100-pair rational certificate and its source-tree
bridge. It does not supply the still-missing `f0Lo`/`g` packet hypotheses. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapExcludedTree2337
open Finset ConvexMinorantCore DBMMinorantDual
noncomputable section

theorem excluded_2337_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2337 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapCertificates.F0_2337)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapCertificates.G_2337 q) : False := by
  apply FrozenCapCertificates.excluded_2337 p hp hf0 hg
  intro a
  have hrow := FrozenCapRowCap2337.row_cap (p.rowFrom a) (p.rowTo a)
  have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2337
    (p.rowFrom a) (p.rowTo a)
  simpa only [hnode, DBMMinorantDual.db, hbridge,
    DBMMinorantDual.rowA, FrozenCapRowCap2337.rowA,
    FrozenCapCertificates.y_2337, FrozenCapRationalCore.y_2337] using hrow

end
end N11Formalization.FrozenCapExcludedTree2337
#check @N11Formalization.FrozenCapExcludedTree2337.excluded_2337_tree
#print axioms N11Formalization.FrozenCapExcludedTree2337.excluded_2337_tree
