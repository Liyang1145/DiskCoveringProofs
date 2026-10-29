import N11Formalization.FrozenCapCertificates
import N11Formalization.FrozenCapRowCap2341
import N11Formalization.FrozenCapRowCapTreeBridges

/-! Node-identity wrapper for the frozen-cap exclusion at public node 2341.

`FrozenCapCertificates.excluded_2341` is stated for an arbitrary packet node.
This module fixes `p.nodeID` to the frozen source node and derives the row-cap
hypothesis from the exact 100-pair rational certificate and its source-tree
bridge. It does not supply the still-missing `f0Lo`/`g` packet hypotheses. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapExcludedTree2341
open Finset ConvexMinorantCore DBMMinorantDual
noncomputable section

theorem excluded_2341_tree {m : ℕ} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p)
    (hnode : p.nodeID = (2341 : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapCertificates.F0_2341)
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapCertificates.G_2341 q) : False := by
  apply FrozenCapCertificates.excluded_2341 p hp hf0 hg
  intro a
  have hrow := FrozenCapRowCap2341.row_cap (p.rowFrom a) (p.rowTo a)
  have hbridge := FrozenCapRowCapTreeBridges.db_eq_tree_2341
    (p.rowFrom a) (p.rowTo a)
  simpa only [hnode, DBMMinorantDual.db, hbridge,
    DBMMinorantDual.rowA, FrozenCapRowCap2341.rowA,
    FrozenCapCertificates.y_2341, FrozenCapRationalCore.y_2341] using hrow

end
end N11Formalization.FrozenCapExcludedTree2341
#check @N11Formalization.FrozenCapExcludedTree2341.excluded_2341_tree
#print axioms N11Formalization.FrozenCapExcludedTree2341.excluded_2341_tree
