#!/usr/bin/env python3
"""Split lane-B frozen-cap row proofs into bounded row declarations.

The generated module keeps the frozen matrix and row-cap statement byte-for-byte
through `def db`; only the proof ending is regenerated.  All arithmetic checks
are exact and run before any file is written.
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
    match = re.search(r"def dbmVal.*?=> !\[\s*\n(.*?)\n  \] i j", text, re.S)
    assert match, node
    rows = []
    for line in match.group(1).splitlines():
        row = re.search(r"!\[(.*)\]", line)
        if row:
            rows.append([int(value) for value in row.group(1).split(",")])
    assert len(rows) == 10 and all(len(row) == 10 for row in rows), node
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


def split_proof(text: str, node: int, y: list[Fraction],
                matrix: list[list[int]]) -> str:
    match = re.search(r"\ntheorem row_cap(?:_\d+_\d+|_\d+ | \()", text)
    assert match, node
    head = text[:match.start() + 1]
    leaves = []
    for i in range(10):
        for j in range(10):
            terms = " + ".join(
                f"y_{node} {q} * rowA {i} {j} {q}" for q in range(9))
            leaves.append(f'''theorem row_cap_{node}_{i}_{j} :
    {terms} ≤ db {i} {j} := by
  decide +kernel''')
    rows = []
    for i in range(10):
        cases = "\n".join(
            f"    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] "
            f"using row_cap_{node}_{i}_{j}" for j in range(10))
        rows.append(f'''theorem row_cap_{i} (j : Fin 10) :
    (∑ q : Fin 9, y_{node} q * rowA {i} j q) ≤ db {i} j := by
  fin_cases j <;>
    first
{cases}''')
    dispatch = "\n".join(f"  · exact row_cap_{i} j" for i in range(10))
    return head + "\n\n".join(leaves) + "\n\n" + "\n\n".join(rows) + f'''

theorem row_cap (i j : Fin 10) :
    (∑ q : Fin 9, y_{node} q * rowA i j q) ≤ db i j := by
  fin_cases i
{dispatch}

end
end N11Formalization.LaneBFrozenCapRowCap{node}
#check @N11Formalization.LaneBFrozenCapRowCap{node}.row_cap
#print axioms N11Formalization.LaneBFrozenCapRowCap{node}.row_cap
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="check only; do not rewrite")
    args = parser.parse_args()
    checks = []
    outputs = {}
    for node in NODES:
        path = LEAN / f"LaneBFrozenCapRowCap{node}.lean"
        text = path.read_text()
        y = parse_y(node)
        matrix = parse_matrix(text, node)
        checks.append(check_exact(node, y, matrix))
        outputs[path] = split_proof(text, node, y, matrix)
    if not args.check:
        for path, text in outputs.items():
            path.write_text(text)
    else:
        stale = [str(path) for path, text in outputs.items()
                 if path.read_text() != text]
        assert not stale, stale
    hashes = {path.name: hashlib.sha256(text.encode()).hexdigest().upper()
              for path, text in outputs.items()}
    print(json.dumps({"ok": True, "checks": checks,
                      "leaf_proofs_per_module": 100,
                      "rewritten": not args.check, "sha256": hashes}, indent=2))


if __name__ == "__main__":
    main()
