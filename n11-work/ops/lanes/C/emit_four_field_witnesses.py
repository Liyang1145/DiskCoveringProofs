#!/usr/bin/env python3
"""Emit the five corrected four-field rescue witnesses exactly and deterministically."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common

IDS = (1409, 2337, 2341, 2368, 2370)
REPORT = HERE / "residual-mixture-faces4.json"
OUT = ROOT / "n11-work/lean/N11Formalization/FrozenCapFourFieldWitnesses.lean"


def lean_rat(q):
    return f"({q.numerator} : ℚ) / {q.denominator}" if q.denominator != 1 else f"({q.numerator} : ℚ)"


def load():
    doc = json.loads(REPORT.read_text())
    recs = {r["id"]: r for r in doc["records"] if r["status"] == "PASS"}
    assert set(recs) == set(IDS) and doc["pass_count"] == len(IDS)
    source = {r["id"]: r for r in json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))["records"]}
    text = common.DBM.read_text()
    out = []
    for node in IDS:
        r = recs[node]
        ep = [common.endpoint_lo(Q(v)) for v in source[node]["g"]]
        y = [Q(0)] * 9
        for k, field in enumerate(r["support"][:3]):
            y[field] = Q(r["coordinates"][k])
        y[r["support"][3]] = 1 - sum(y)
        assert all(v >= 0 for v in y) and sum(y) == 1
        db = common.parse_db(text, node)
        for i in range(10):
            for j in range(10):
                rhs = Q(db[i][j], 4096)
                lhs = sum(y[q] * common.row_a(i, j, q) for q in range(9))
                assert lhs <= rhs, (node, i, j, lhs, rhs)
        out.append((node, y, ep))
    return out


def main():
    records = load()
    blocks = []
    for node, y, ep in records:
        vec = ", ".join(lean_rat(v) for v in y)
        weighted = [y[q] * ep[q] for q in range(9)]
        blocks.append(f'''def y4_{node} : Fin 9 → ℚ :=
  ![{vec}]

theorem nonneg_{node} : ∀ q, 0 ≤ y4_{node} q := by
  intro q; fin_cases q <;> norm_num [y4_{node}]

theorem sum_{node} : (∑ q : Fin 9, y4_{node} q) = 1 := by
  norm_num [y4_{node}, Fin.sum_univ_succ]

theorem endpoint_{node} (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_{node} q) = E_{node} q := by
  fin_cases q <;> norm_num [G_{node}, E_{node}, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H4_{node} : Fin 9 → ℚ := ![{", ".join(lean_rat(v) for v in weighted)}]

theorem weighted_terms_{node} (q : Fin 9) : y4_{node} q * E_{node} q = H4_{node} q := by
  fin_cases q <;> norm_num [y4_{node}, E_{node}, H4_{node}]

theorem strict_gain_{node} : F0_{node} + ∑ q : Fin 9, y4_{node} q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_{node} q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_{node}]
  have hsum : (∑ q : Fin 9, y4_{node} q * E_{node} q) = ∑ q : Fin 9, H4_{node} q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_{node} q
  rw [hsum]
  norm_num [F0_{node}, H4_{node}, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]''')
    src = '''import N11Formalization.FrozenCapRationalCore
import N11Formalization.PaidCellCertificateMCap

/-! Corrected four-field rescue witnesses from `residual_mixture_faces4.py`.
These reuse the exact `F0`, `G`, and `E` data from the green rational core;
only the unit-sum mixture `y` changes. Generated deterministically by
`ops/lanes/C/emit_four_field_witnesses.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldWitnesses
open Finset
open ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

''' + "\n\n".join(blocks) + '''

end
end N11Formalization.FrozenCapFourFieldWitnesses

#check @N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_1409
#check @N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_2370
#print axioms N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_1409
#print axioms N11Formalization.FrozenCapFourFieldWitnesses.strict_gain_2370
'''
    OUT.write_text(src)
    print("wrote", OUT.relative_to(ROOT))
    print("sha256", hashlib.sha256(OUT.read_bytes()).hexdigest().upper())
    print("exact witnesses", len(records), "row caps", 100 * len(records))


if __name__ == "__main__":
    main()
