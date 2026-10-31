#!/usr/bin/env python3
"""Emit the exact five-field 2368 witness and 100 frozen-db row caps."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common

NODE = 2368
REPORT = HERE / "residual-mixture-faces5-float-2360-2368-2370.json"
OUT = ROOT / "n11-work/lean/N11Formalization/FrozenCapFiveField2368.lean"


def lean_rat(q):
    return f"({q.numerator} : ℚ) / {q.denominator}" if q.denominator != 1 else f"({q.numerator} : ℚ)"


def load():
    report = json.loads(REPORT.read_text())
    assert report["proposal_sha256"] == hashlib.sha256(common.PROPOSAL.read_bytes()).hexdigest().upper()
    assert report["dbm_sha256"] == hashlib.sha256(common.DBM.read_bytes()).hexdigest().upper()
    rec = {r["id"]: r for r in report["records"]}[NODE]
    assert rec["status"] == "PASS" and Q(rec["exact_margin"]) < 0
    source = {r["id"]: r for r in json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))["records"]}[NODE]
    support, coords = rec["support"], [Q(v) for v in rec["coordinates"]]
    assert len(support) == 5 and len(coords) == 4
    y = [Q(0)] * 9
    for k, field in enumerate(support[:4]):
        y[field] = coords[k]
    y[support[4]] = 1 - sum(coords)
    assert all(v >= 0 for v in y) and sum(y) == 1
    db = common.parse_db(common.DBM.read_text(), NODE)
    slacks = [Q(db[i][j], 4096) - sum(y[q] * common.row_a(i, j, q) for q in range(9))
              for i in range(10) for j in range(10)]
    assert min(slacks) >= 0
    ep = [common.endpoint_lo(Q(v)) for v in source["g"]]
    gain = sum(y[q] * ep[q] for q in range(9))
    assert Q(source["f0Lo"]) + gain < common.T2
    return y, ep, min(slacks), Q(source["f0Lo"]) + gain


def main():
    y, ep, min_slack, lhs = load()
    vec = ", ".join(lean_rat(v) for v in y)
    weighted = [y[q] * ep[q] for q in range(9)]
    caps = []
    for i in range(10):
        for j in range(10):
            caps.append(f'''theorem row_cap_{i}_{j} :
    (∑ q : Fin 9, y5_2368 q * FrozenCapRowCap2368.rowA {i} {j} q) ≤
      FrozenCapRowCap2368.db {i} {j} := by
  norm_num [y5_2368, FrozenCapRowCap2368.rowA, FrozenCapRowCap2368.db,
    Fin.sum_univ_succ]''')
    rows = []
    for i in range(10):
        cases = "\n".join(f"  · exact row_cap_{i}_{j}" for j in range(10))
        rows.append(f'''theorem row_cap_{i} (j : Fin 10) :
    (∑ q : Fin 9, y5_2368 q * FrozenCapRowCap2368.rowA {i} j q) ≤
      FrozenCapRowCap2368.db {i} j := by
  fin_cases j
{cases}''')
    src = f'''import N11Formalization.FrozenCapRationalCore
import N11Formalization.FrozenCapRowCap2368

/-! Exact five-field rescue witness for residual node 2368, with all 100
row caps against the frozen `DBMSourceTree` matrix. Generated deterministically
by `ops/lanes/C/emit_five_field_2368.py`; this does not claim packet existence. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveField2368
open Finset ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

def y5_2368 : Fin 9 → ℚ := ![{vec}]

theorem nonneg_2368 : ∀ q, 0 ≤ y5_2368 q := by
  intro q; fin_cases q <;> norm_num [y5_2368]

theorem sum_2368 : (∑ q : Fin 9, y5_2368 q) = 1 := by
  norm_num [y5_2368, Fin.sum_univ_succ]

theorem endpoint_2368 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2368 q) = E_2368 q := by
  fin_cases q <;> norm_num [G_2368, E_2368, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H5_2368 : Fin 9 → ℚ := ![{", ".join(lean_rat(v) for v in weighted)}]

theorem weighted_terms_2368 (q : Fin 9) : y5_2368 q * E_2368 q = H5_2368 q := by
  fin_cases q <;> norm_num [y5_2368, E_2368, H5_2368]

theorem strict_gain_2368 : F0_2368 + ∑ q : Fin 9, y5_2368 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2368 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2368]
  have hsum : (∑ q : Fin 9, y5_2368 q * E_2368 q) = ∑ q : Fin 9, H5_2368 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2368 q
  rw [hsum]
  norm_num [F0_2368, H5_2368, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

{chr(10).join(caps)}

{chr(10).join(rows)}

theorem row_cap_2368 (i j : Fin 10) :
    (∑ q : Fin 9, y5_2368 q * FrozenCapRowCap2368.rowA i j q) ≤
      FrozenCapRowCap2368.db i j := by
  fin_cases i
{chr(10).join(f"  · exact row_cap_{i} j" for i in range(10))}

end
end N11Formalization.FrozenCapFiveField2368

#check @N11Formalization.FrozenCapFiveField2368.strict_gain_2368
#check @N11Formalization.FrozenCapFiveField2368.row_cap_2368
#print axioms N11Formalization.FrozenCapFiveField2368.strict_gain_2368
#print axioms N11Formalization.FrozenCapFiveField2368.row_cap_2368
'''
    OUT.write_text(src)
    print(OUT.relative_to(ROOT), hashlib.sha256(OUT.read_bytes()).hexdigest().upper())
    print("rows", 100, "min_slack", min_slack, "lhs", lhs, "gap", lhs - common.T2)


if __name__ == "__main__":
    main()
