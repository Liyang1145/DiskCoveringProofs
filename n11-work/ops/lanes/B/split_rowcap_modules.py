#!/usr/bin/env python3
"""Emit thin lane-B aliases over the kernel-green frozen-cap row modules.

The seven `FrozenCapRowCap*` modules are already serialized in CI.  Re-proving
their 700 leaves here duplicated those goals and produced `unsolved goals`.
This emitter keeps the independent exact-rational audit, but emits only a
type-preserving alias of each module's final `row_cap` theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
CORE = LEAN / "FrozenCapRationalCore.lean"
PROBE = LEAN / "LaneBRowCapDecideProbe.lean"
NODES = (1409, 2337, 2341, 2356, 2360, 2368, 2370)


def parse_y(node: int) -> list[Fraction]:
    line = next(line for line in CORE.read_text().splitlines()
                if line.startswith(f"def y_{node} "))
    payload = line.split(":= ![", 1)[1].rsplit("]", 1)[0]
    values = []
    for item in payload.split(","):
        item = item.strip().replace("(", "").replace(")", "").replace(" : ℚ", "")
        values.append(Fraction(item))
    assert len(values) == 9, (node, len(values))
    return values


def parse_matrix(text: str, node: int) -> list[list[int]]:
    match = re.search(r"def db : Fin 10 → Fin 10 → ℚ\n(.*?)\n\ntheorem row_cap", text, re.S)
    assert match, node
    rows = [[None] * 10 for _ in range(10)]
    for line in match.group(1).splitlines():
        cell = re.match(r"  \| ⟨(\d+), _⟩, ⟨(\d+), _⟩ => (.*)$", line)
        if not cell:
            continue
        i, j = int(cell.group(1)), int(cell.group(2))
        rhs = re.fullmatch(r"(-?\d+) : ℚ\n?|\((-?\d+) : ℚ\)(?: / (\d+))?", cell.group(3))
        assert rhs, (node, line)
        numerator = int(rhs.group(1) or rhs.group(2))
        value = Fraction(numerator, int(rhs.group(3) or 1))
        assert (value * 4096).denominator == 1, (node, line)
        rows[i][j] = (value * 4096).numerator
    assert all(value is not None for row in rows for value in row), node
    return rows


def check_exact(node: int, y: list[Fraction], matrix: list[list[int]]) -> dict:
    assert sum(y) == 1, (node, sum(y))
    violations = []
    for i in range(10):
        for j in range(10):
            lhs = sum(y[q] * ((q < j) - (q < i)) for q in range(9))
            rhs = Fraction(matrix[i][j], 4096)
            if lhs > rhs:
                violations.append({"row": i, "col": j, "lhs": str(lhs), "rhs": str(rhs)})
    assert not violations, (node, violations)
    return {"node": node, "ordered_pairs": 100, "weight_sum": str(sum(y)),
            "violations": violations}


def lean_rat(q: Fraction) -> str:
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} : ℚ) / {q.denominator}"


def split_proof(text: str, node: int) -> str:
    match = re.search(r"\ntheorem row_cap(?:_\d+_\d+|_\d+ | \()", text)
    assert match, node
    return f'''import N11Formalization.FrozenCapRowCap{node}

/-! Thin lane-B alias for the CI-green frozen node {node} row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBFrozenCapRowCap{node}
open N11Formalization.FrozenCapRowCap{node}
noncomputable section

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, y_{node} q * rowA i j q) ≤ db i j :=
  N11Formalization.FrozenCapRowCap{node}.row_cap i j

end
end N11Formalization.LaneBFrozenCapRowCap{node}
#check @N11Formalization.LaneBFrozenCapRowCap{node}.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap{node}.row_cap
'''


def probe_proof() -> str:
    leaves = "\n\n".join(f'''theorem row_{i}_{j} :
    (∑ q : Fin 9, y_1409 q * rowA {i} {j} q) ≤ db {i} {j} :=
  N11Formalization.FrozenCapRowCap1409.row_cap {i} {j}''' for i, j in ((0, 1), (4, 5), (9, 9)))
    return f'''import N11Formalization.FrozenCapRowCap1409

/-! Representative lane-B aliases for the frozen node 1409 row cap. -/
set_option autoImplicit false
namespace N11Formalization.LaneBRowCapDecideProbe
open N11Formalization.FrozenCapRowCap1409
noncomputable section

{leaves}

end
end N11Formalization.LaneBRowCapDecideProbe
#print axioms N11Formalization.LaneBRowCapDecideProbe.row_4_5
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="check only; do not rewrite")
    args = parser.parse_args()
    checks = []
    outputs = {}
    for node in NODES:
        path = LEAN / f"LaneBFrozenCapRowCap{node}.lean"
        source = LEAN / f"FrozenCapRowCap{node}.lean"
        text = source.read_text()
        y = parse_y(node)
        matrix = parse_matrix(text, node)
        checks.append(check_exact(node, y, matrix))
        outputs[path] = split_proof(text, node)
    outputs[PROBE] = probe_proof()
    if not args.check:
        for path, text in outputs.items():
            path.write_text(text)
    else:
        stale = [str(path) for path, text in outputs.items()
                 if path.read_text() != text]
        assert not stale, stale
    hashes = {path.name: hashlib.sha256(text.encode()).hexdigest().upper()
              for path, text in outputs.items()}
    print(json.dumps({"ok": True,
                      "scope": "exact-rational audit and deterministic alias emission only; no Lean elaboration or proof credit",
                      "checks": checks,
                      "audited_caps_per_module": 100,
                      "rewritten": not args.check, "sha256": hashes}, indent=2))


if __name__ == "__main__":
    main()
