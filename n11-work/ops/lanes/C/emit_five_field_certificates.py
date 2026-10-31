#!/usr/bin/env python3
"""Emit exact five-field witnesses and row caps for residual IDs 2356/2360."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common

IDS = (2356, 2360)
REPORT = HERE / "residual-mixture-faces5-float-2356-2360.json"
WITNESSES = ROOT / "n11-work/lean/N11Formalization/FrozenCapFiveFieldWitnesses.lean"
ROW_CAPS = ROOT / "n11-work/lean/N11Formalization/FrozenCapFiveFieldRowCaps.lean"


def lean_rat(q):
    return f"({q.numerator} : ℚ) / {q.denominator}" if q.denominator != 1 else f"({q.numerator} : ℚ)"


def load():
    doc = json.loads(REPORT.read_text())
    recs = {r["id"]: r for r in doc["records"] if r["status"] == "PASS"}
    assert set(recs) == set(IDS) and doc["pass_count"] == len(IDS)
    source = {r["id"]: r for r in json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))["records"]}
    db_text = common.DBM.read_text()
    out = []
    for node in IDS:
        r = recs[node]
        ep = [common.endpoint_lo(Q(v)) for v in source[node]["g"]]
        support = r["support"]
        coords = [Q(v) for v in r["coordinates"]]
        y = [Q(0)] * 9
        for k, field in enumerate(support[:4]):
            y[field] = coords[k]
        y[support[4]] = 1 - sum(coords)
        assert all(v >= 0 for v in y) and sum(y) == 1
        db = common.parse_db(db_text, node)
        slacks = []
        for i in range(10):
            for j in range(10):
                lhs = sum(y[q] * common.row_a(i, j, q) for q in range(9))
                rhs = Q(db[i][j], 4096)
                assert lhs <= rhs, (node, i, j, lhs, rhs)
                slacks.append(rhs - lhs)
        out.append((node, y, db, min(slacks), ep))
    return out


def emit_witnesses(records):
    blocks = []
    for node, y, _, _, ep in records:
        vec = ", ".join(lean_rat(v) for v in y)
        weighted = [y[q] * ep[q] for q in range(9)]
        blocks.append(f'''def y5_{node} : Fin 9 → ℚ := ![{vec}]

theorem nonneg_{node} : ∀ q, 0 ≤ y5_{node} q := by
  intro q; fin_cases q <;> norm_num [y5_{node}]

theorem sum_{node} : (∑ q : Fin 9, y5_{node} q) = 1 := by
  norm_num [y5_{node}, Fin.sum_univ_succ]

theorem endpoint_{node} (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_{node} q) = E_{node} q := by
  fin_cases q <;> norm_num [G_{node}, E_{node}, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H5_{node} : Fin 9 → ℚ := ![{", ".join(lean_rat(v) for v in weighted)}]

theorem weighted_terms_{node} (q : Fin 9) : y5_{node} q * E_{node} q = H5_{node} q := by
  fin_cases q <;> norm_num [y5_{node}, E_{node}, H5_{node}]

theorem strict_gain_{node} : F0_{node} + ∑ q : Fin 9, y5_{node} q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_{node} q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_{node}]
  have hsum : (∑ q : Fin 9, y5_{node} q * E_{node} q) = ∑ q : Fin 9, H5_{node} q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_{node} q
  rw [hsum]
  norm_num [F0_{node}, H5_{node}, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]''')
    src = '''import N11Formalization.FrozenCapRationalCore
import N11Formalization.PaidCellCertificateMCap

/-! Exact five-field rescue witnesses for residual nodes 2356 and 2360.
Generated from the exact-rational recheck report by
`ops/lanes/C/emit_five_field_certificates.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveFieldWitnesses
open Finset ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

''' + "\n\n".join(blocks) + '''

end
end N11Formalization.FrozenCapFiveFieldWitnesses

#check @N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2356
#check @N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2360
#print axioms N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2356
#print axioms N11Formalization.FrozenCapFiveFieldWitnesses.strict_gain_2360
'''
    WITNESSES.write_text(src)


def emit_row_caps(records):
    blocks = []
    for node, y, db, _, _ in records:
        db_cases = "\n  ".join(
            f"| ⟨{i}, _⟩, ⟨{j}, _⟩ => {lean_rat(Q(db[i][j], 4096))}"
            for i in range(10) for j in range(10))
        leaves = []
        for i in range(10):
            for j in range(10):
                lhs_q = sum(y[q] * common.row_a(i, j, q) for q in range(9))
                lhs = " + ".join(
                    f"y5_{node} ({q} : Fin 9) * rowA ({i} : Fin 10) ({j} : Fin 10) ({q} : Fin 9)"
                    for q in range(9))
                rhs = Q(db[i][j], 4096)
                leaves.append(f'''theorem row_cap_{node}_{i}_{j} :
    {lhs} ≤ db_{node} {i} {j} := by
  change {lean_rat(lhs_q)} ≤ {lean_rat(rhs)}
  norm_num''')
        row_lemmas = []
        for i in range(10):
            row_lemmas.append(f'''theorem row_cap_{node}_{i} (j : Fin 10) :
    (∑ q : Fin 9, y5_{node} q * rowA {i} j q) ≤ db_{node} {i} j := by
  fin_cases j <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] <;>
    first
    | exact row_cap_{node}_{i}_0
    | exact row_cap_{node}_{i}_1
    | exact row_cap_{node}_{i}_2
    | exact row_cap_{node}_{i}_3
    | exact row_cap_{node}_{i}_4
    | exact row_cap_{node}_{i}_5
    | exact row_cap_{node}_{i}_6
    | exact row_cap_{node}_{i}_7
    | exact row_cap_{node}_{i}_8
    | exact row_cap_{node}_{i}_9''')
        blocks.append(f'''def db_{node} : Fin 10 → Fin 10 → ℚ
  {db_cases}

{chr(10).join(leaves)}

{chr(10).join(row_lemmas)}

theorem row_cap_{node} (i j : Fin 10) :
    (∑ q : Fin 9, y5_{node} q * rowA i j q) ≤ db_{node} i j := by
  fin_cases i
{chr(10).join(f"  · exact row_cap_{node}_{i} j" for i in range(10))}''')
    src = '''import N11Formalization.FrozenCapFiveFieldWitnesses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact 100-pair caps for the two five-field witnesses. Generated by
`ops/lanes/C/emit_five_field_certificates.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveFieldRowCaps
open Finset
open N11Formalization.FrozenCapFiveFieldWitnesses
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

''' + "\n\n".join(blocks) + '''

end
end N11Formalization.FrozenCapFiveFieldRowCaps

#check @N11Formalization.FrozenCapFiveFieldRowCaps.row_cap_2356
#check @N11Formalization.FrozenCapFiveFieldRowCaps.row_cap_2360
#print axioms N11Formalization.FrozenCapFiveFieldRowCaps.row_cap_2356
#print axioms N11Formalization.FrozenCapFiveFieldRowCaps.row_cap_2360
'''
    ROW_CAPS.write_text(src)


def main():
    records = load()
    emit_witnesses(records)
    emit_row_caps(records)
    for path in (WITNESSES, ROW_CAPS):
        print(path.relative_to(ROOT), hashlib.sha256(path.read_bytes()).hexdigest().upper())
    print("rows", 100 * len(records), "per_node_min_slack", [(n, str(s)) for n, _, _, s, _ in records])


if __name__ == "__main__":
    main()
