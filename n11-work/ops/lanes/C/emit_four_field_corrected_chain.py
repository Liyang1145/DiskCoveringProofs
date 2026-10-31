#!/usr/bin/env python3
"""Emit corrected four-field row caps and their three exclusion consumers."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common

IDS = (1409, 2337, 2341)
REPORT = HERE / "residual-mixture-faces4.json"
OUT_ROWS = ROOT / "n11-work/lean/N11Formalization/FrozenCapFourFieldCorrectedRowCaps.lean"
OUT_TREE = ROOT / "n11-work/lean/N11Formalization/FrozenCapFourFieldCorrectedTree.lean"


def lean_rat(q: Q) -> str:
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} : ℚ) / {q.denominator}"


def main():
    report = json.loads(REPORT.read_text())
    records = {r["id"]: r for r in report["records"] if r["status"] == "PASS"}
    assert set(records) == set(IDS) and report["pass_count"] == len(IDS)
    proposal = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    source = {r["id"]: r for r in proposal["records"]}
    dbm = common.DBM.read_text()

    blocks, checks = [], []
    for node in IDS:
        rec = records[node]
        ep = [common.endpoint_lo(Q(v)) for v in source[node]["g"]]
        y = [Q(0)] * 9
        for k, field in enumerate(rec["support"][:3]):
            y[field] = Q(rec["coordinates"][k])
        y[rec["support"][3]] = 1 - sum(y)
        assert all(v >= 0 for v in y) and sum(y) == 1
        db = common.parse_db(dbm, node)
        slacks = []
        for i in range(10):
            for j in range(10):
                lhs = sum(y[q] * common.row_a(i, j, q) for q in range(9))
                rhs = Q(db[i][j], 4096)
                assert lhs <= rhs, (node, i, j, lhs, rhs)
                slacks.append(rhs - lhs)
        gain = sum(y[q] * ep[q] for q in range(9))
        assert gain < common.T2 - Q(source[node]["f0Lo"]), (node, gain)
        checks.append((node, min(slacks), common.T2 - Q(source[node]["f0Lo"]) - gain))

        cases = "\n  ".join(
            f"| ⟨{i}, _⟩, ⟨{j}, _⟩ => {lean_rat(Q(db[i][j], 4096))}"
            for i in range(10) for j in range(10))
        leaves = []
        for i in range(10):
            for j in range(10):
                leaves.append(f'''theorem row_cap_{node}_{i}_{j} :
    (∑ q : Fin 9, y4_{node} q * rowA {i} {j} q) ≤ db_{node} {i} {j} := by
  norm_num [y4_{node}, rowA, db_{node}, Fin.sum_univ_succ]''')
        rows = []
        for i in range(10):
            branches = "\n".join(f"  · exact row_cap_{node}_{i}_{j}" for j in range(10))
            rows.append(f'''theorem row_cap_{node}_{i} (j : Fin 10) :
    (∑ q : Fin 9, y4_{node} q * rowA {i} j q) ≤ db_{node} {i} j := by
  fin_cases j
{branches}''')
        ibranches = "\n".join(f"  · exact row_cap_{node}_{i} j" for i in range(10))
        blocks.append(f'''def db_{node} : Fin 10 → Fin 10 → ℚ
  {cases}

''' + "\n\n".join(leaves) + "\n\n" + "\n\n".join(rows) + f'''

theorem row_cap_{node} (i j : Fin 10) :
    (∑ q : Fin 9, y4_{node} q * rowA i j q) ≤ db_{node} i j := by
  fin_cases i
{ibranches}''')

    row_src = '''import N11Formalization.FrozenCapFourFieldWitnessesCorrected
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact 100-pair row caps for the three corrected four-field witnesses. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldCorrectedRowCaps
open Finset
open N11Formalization.FrozenCapFourFieldWitnessesCorrected
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

''' + "\n\n".join(blocks) + '''

end
end N11Formalization.FrozenCapFourFieldCorrectedRowCaps

#check @N11Formalization.FrozenCapFourFieldCorrectedRowCaps.row_cap_1409
#check @N11Formalization.FrozenCapFourFieldCorrectedRowCaps.row_cap_2341
'''
    OUT_ROWS.write_text(row_src)

    bridges, exclusions = [], []
    for node in IDS:
        bridges.append(f'''theorem db_eq_tree_{node} : ∀ i j : Fin 10,
    (((N11Formalization.DBMSourceTree.data ({node} : Fin 5011)).db i j : ℚ) / 4096) =
      N11Formalization.FrozenCapFourFieldCorrectedRowCaps.db_{node} i j := by
  decide +kernel''')
        exclusions.append(f'''theorem excluded_{node}_tree {{m : ℕ}} (p : PaidCellCertificateM.Packet m)
    (hp : PaidCellCertificateM.Valid p) (hnode : p.nodeID = ({node} : Fin 5011))
    (hf0 : f0Lo (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p)
      (PaidCellCertificateM.interQ p) = FrozenCapRationalCore.F0_{node})
    (hg : ∀ q, g (PaidCellCertificateM.W p) (PaidCellCertificateM.slopeQ p) q =
      FrozenCapRationalCore.G_{node} q) : False := by
  apply PaidCellCertificateMCap.not_valid_of_frozen_cap p hp
    FrozenCapRationalCore.F0_{node} FrozenCapRationalCore.G_{node}
    FrozenCapFourFieldWitnessesCorrected.y4_{node} hf0 hg
    FrozenCapFourFieldWitnessesCorrected.nonneg_{node}
    FrozenCapFourFieldWitnessesCorrected.sum_{node}
  · intro a
    have hrow := FrozenCapFourFieldCorrectedRowCaps.row_cap_{node}
      (p.rowFrom a) (p.rowTo a)
    have hbridge := db_eq_tree_{node} (p.rowFrom a) (p.rowTo a)
    simpa only [hnode, DBMMinorantDual.db, hbridge,
      DBMMinorantDual.rowA, FrozenCapFourFieldCorrectedRowCaps.rowA,
      FrozenCapFourFieldWitnessesCorrected.y4_{node}] using hrow
  · simpa only [FrozenCapRationalCore.T,
      N11Formalization.FlashCosineLeaf284Bridge.T] using
      FrozenCapFourFieldWitnessesCorrected.strict_gain_{node}''')

    tree_src = '''import N11Formalization.DBMSourceTreeData
import N11Formalization.FrozenCapFourFieldCorrectedRowCaps
import N11Formalization.PaidCellCertificateMCap

/-! Conditional exclusions from the three corrected four-field witnesses. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldCorrectedTree
open ConvexMinorantCore DBMMinorantDual
noncomputable section

''' + "\n\n".join(bridges) + "\n\n" + "\n\n".join(exclusions) + '''

end
end N11Formalization.FrozenCapFourFieldCorrectedTree

#check @N11Formalization.FrozenCapFourFieldCorrectedTree.excluded_1409_tree
#check @N11Formalization.FrozenCapFourFieldCorrectedTree.excluded_2341_tree
'''
    OUT_TREE.write_text(tree_src)
    print("row_caps", OUT_ROWS.relative_to(ROOT), hashlib.sha256(OUT_ROWS.read_bytes()).hexdigest())
    print("tree", OUT_TREE.relative_to(ROOT), hashlib.sha256(OUT_TREE.read_bytes()).hexdigest())
    print("checks node/min_row_slack/gain_margin", checks)


if __name__ == "__main__":
    main()
