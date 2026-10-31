#!/usr/bin/env python3
"""Emit the five corrected four-field 100-pair row-cap modules."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import recheck_next512_rows as common

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
DBM = ROOT / "n11-work/lean/N11Formalization/DBMSourceTreeData.lean"
OUT = ROOT / "n11-work/lean/N11Formalization/FrozenCapFourFieldRowCaps.lean"
IDS = (1409, 2337, 2341, 2368, 2370)


def lean_rat(q: Q) -> str:
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} : ℚ) / {q.denominator}"


def main():
    doc = json.loads((HERE / "residual-mixture-faces4.json").read_text())
    recs = {r["id"]: r for r in doc["records"] if r["status"] == "PASS"}
    assert set(recs) == set(IDS) and len(recs) == 5
    text = common.DBM.read_text()
    blocks = []
    checks = []
    for node in IDS:
        r = recs[node]
        y = [Q(0)] * 9
        for k, field in enumerate(r["support"][:3]):
            y[field] = Q(r["coordinates"][k])
        y[r["support"][3]] = 1 - sum(y)
        assert all(v >= 0 for v in y) and sum(y) == 1
        db = common.parse_db(text, node)
        slacks = []
        for i in range(10):
            for j in range(10):
                lhs = sum(y[q] * common.row_a(i, j, q) for q in range(9))
                rhs = Q(db[i][j], 4096)
                assert lhs <= rhs, (node, i, j, lhs, rhs)
                slacks.append(rhs - lhs)
        checks.append((node, min(slacks)))
        cases = "\n  ".join(
            f"| ⟨{i}, _⟩, ⟨{j}, _⟩ => {lean_rat(Q(db[i][j], 4096))}"
            for i in range(10) for j in range(10))
        leaves = []
        for i in range(10):
            for j in range(10):
                rhs = Q(db[i][j], 4096)
                leaves.append(f'''theorem row_cap_{node}_{i}_{j} :
    (∑ q : Fin 9, y4_{node} q * rowA {i} {j} q) ≤ db_{node} {i} {j} := by
  norm_num [y4_{node}, rowA, db_{node}, Fin.sum_univ_succ]''')
        row_lemmas = []
        for i in range(10):
            branches = "\n".join(
                f"  · exact row_cap_{node}_{i}_{j}" for j in range(10))
            row_lemmas.append(f'''theorem row_cap_{node}_{i} (j : Fin 10) :
    (∑ q : Fin 9, y4_{node} q * rowA {i} j q) ≤ db_{node} {i} j := by
  fin_cases j
{branches}''')
        i_branches = "\n".join(
            f"  · exact row_cap_{node}_{i} j" for i in range(10))
        blocks.append(f'''def db_{node} : Fin 10 → Fin 10 → ℚ
  {cases}

''' + "\n\n".join(leaves) + f'''

''' + "\n\n".join(row_lemmas) + f'''

theorem row_cap_{node} (i j : Fin 10) :
    (∑ q : Fin 9, y4_{node} q * rowA i j q) ≤ db_{node} i j := by
  fin_cases i
{i_branches}''')
    src = '''import N11Formalization.FrozenCapFourFieldWitnesses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact 100-pair row caps for the five corrected four-field witnesses.
Generated deterministically by `ops/lanes/C/emit_four_field_row_caps.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldRowCaps
open Finset
open N11Formalization.FrozenCapFourFieldWitnesses
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

''' + "\n\n".join(blocks) + '''

end
end N11Formalization.FrozenCapFourFieldRowCaps

#check @N11Formalization.FrozenCapFourFieldRowCaps.row_cap_1409
#check @N11Formalization.FrozenCapFourFieldRowCaps.row_cap_2370
'''
    OUT.write_text(src)
    print("wrote", OUT.relative_to(ROOT))
    print("sha256", hashlib.sha256(OUT.read_bytes()).hexdigest().upper())
    print("rows", len(checks) * 100, "per_node_min_slack", checks)


if __name__ == "__main__":
    main()
