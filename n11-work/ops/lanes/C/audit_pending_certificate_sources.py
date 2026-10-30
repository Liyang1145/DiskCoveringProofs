#!/usr/bin/env python3
"""Cross-check generated four/five-field certificates against frozen sources.

Exact checks only: emitted DBM matrices must equal DBMSourceTreeData, and each
reported witness margin must be positive under rational arithmetic.
"""
from fractions import Fraction as Q
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common

LEAN = ROOT / "n11-work/lean/N11Formalization"
DBM = LEAN / "DBMSourceTreeData.lean"
TREE_TEXT = DBM.read_text()
OUT = HERE / "pending-certificate-source-audit.json"
FOUR = (1409, 2337, 2341, 2368, 2370)
FIVE = (2356, 2360)


def matrix(path, node):
    text = path.read_text()
    m = re.search(rf"def dbmVal_{node} :.*?=> !\[(.*?)\n\s*\] i j", text, re.S)
    if not m:
        raise ValueError(f"matrix {node} not found in {path.name}")
    nums = [int(x) for x in re.findall(r"-?\d+", m.group(1))]
    if len(nums) != 100:
        raise ValueError(f"matrix {node}: {len(nums)} entries")
    return [nums[10 * i:10 * i + 10] for i in range(10)]


def report(path, ids):
    doc = json.loads(path.read_text())
    recs = {}
    for r in doc["records"]:
        if r["id"] in ids and r["status"] == "PASS":
            recs[r["id"]] = r
    if set(recs) != set(ids):
        raise ValueError(f"missing report records in {path.name}: {set(ids) - set(recs)}")
    return recs


def main():
    checks = []
    four_reports = report(HERE / "residual-mixture-faces4.json", FOUR)
    five_reports = report(HERE / "residual-mixture-faces5-float-2356-2360.json", FIVE)
    four_path = LEAN / "FrozenCapFourFieldRowCaps.lean"
    five_path = LEAN / "FrozenCapFiveFieldRowCaps.lean"
    for node, rec, path in ([(n, four_reports[n], four_path) for n in FOUR] +
                            [(n, five_reports[n], five_path) for n in FIVE]):
        emitted = matrix(path, node)
        frozen = common.parse_db(TREE_TEXT, node)
        diffs = [(i, j, emitted[i][j], frozen[i][j]) for i in range(10) for j in range(10)
                 if emitted[i][j] != frozen[i][j]]
        margin = Q(rec["exact_margin"])
        if margin <= 0:
            raise AssertionError(f"{node}: nonpositive witness margin {margin}")
        if diffs:
            raise AssertionError(f"{node}: matrix mismatch {diffs[:3]}")
        checks.append({"id": node, "matrix_mismatches": 0,
                       "exact_margin": str(margin),
                       "support": rec["support"]})
    result = {
        "scope": "HOST exact source cross-check; not a kernel verdict",
        "tree_sha256": hashlib.sha256(DBM.read_bytes()).hexdigest().upper(),
        "four_row_caps_sha256": hashlib.sha256(four_path.read_bytes()).hexdigest().upper(),
        "five_row_caps_sha256": hashlib.sha256(five_path.read_bytes()).hexdigest().upper(),
        "records": len(checks), "matrix_entries_checked": 100 * len(checks),
        "checks": checks,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2))
    for c in checks:
        print(c["id"], "matrix=ok", "margin", c["exact_margin"], "support", c["support"])


if __name__ == "__main__":
    main()
