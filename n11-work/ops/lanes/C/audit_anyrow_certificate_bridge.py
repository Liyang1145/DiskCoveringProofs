#!/usr/bin/env python3
"""Bridge the seven exact arbitrary-row certificates to their Lean modules.

This is a source-level audit, not a kernel verdict.  It checks that each JSON
dual weight vector is the vector used by `FrozenCapRowCap*.row_cap`, that each
copied Lean DBM matrix equals the frozen source matrix, and that all 100 row
caps and the strict gain hold with `Fraction` arithmetic.
"""
from fractions import Fraction as Q
import hashlib
import json
import re
from pathlib import Path

import recheck_next512_rows as common

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
CERT = HERE / "next512-row-cap-certificates.json"
CORE = LEAN / "FrozenCapRationalCore.lean"
OUT = HERE / "anyrow-certificate-bridge-audit.json"
IDS = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
RAT = re.compile(r"\((-?\d+) : ℚ\)(?: / (\d+))?")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def lean_vector(text, name):
    match = re.search(rf"def {name} : Fin 9 → ℚ := !\[(.*)\]", text)
    if not match:
        raise ValueError(f"Lean vector {name} not found")
    values = [Q(int(num), int(den or 1)) for num, den in RAT.findall(match.group(1))]
    if len(values) != 9:
        raise ValueError(f"Lean vector {name}: {len(values)} entries")
    return values


def lean_db(text, node):
    match = re.search(r"def db : Fin 10 → Fin 10 → ℚ(.*?)\ntheorem row_cap_", text, re.S)
    if not match:
        raise ValueError(f"Lean db for {node} not found")
    values = [Q(int(num), int(den or 1)) for num, den in RAT.findall(match.group(1))]
    if len(values) != 100:
        raise ValueError(f"Lean db for {node}: {len(values)} entries")
    return [values[10 * i:10 * i + 10] for i in range(10)]


def main():
    core = CORE.read_text()
    certs = json.loads(CERT.read_text())["certificates"]
    if tuple(cert["id"] for cert in certs) != IDS:
        raise AssertionError("unexpected certificate ids/order")

    checks = []
    for cert in certs:
        node = cert["id"]
        path = LEAN / f"FrozenCapRowCap{node}.lean"
        y_json = [Q(value) for value in cert["weights"]]
        y_lean = lean_vector(core, f"y_{node}")
        if y_lean != y_json:
            raise AssertionError(f"{node}: Lean/JSON weights differ")
        source = common.parse_db(common.DBM.read_text(), node)
        db = lean_db(path.read_text(), node)
        expected = [[Q(source[i][j], 4096) for j in range(10)] for i in range(10)]
        if db != expected:
            raise AssertionError(f"{node}: copied Lean DBM differs from frozen source")
        slacks = [db[i][j] - sum(y_json[q] * common.row_a(i, j, q) for q in range(9))
                  for i in range(10) for j in range(10)]
        if min(slacks) < 0:
            raise AssertionError(f"{node}: negative row-cap slack")
        rec = next(r for r in json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))["records"]
                   if r["id"] == node)
        upper = sum(y_json[q] * common.endpoint_lo(Q(s)) for q, s in enumerate(rec["g"]))
        required = common.T2 - Q(rec["f0Lo"])
        if not upper < required:
            raise AssertionError(f"{node}: strict gain does not hold")
        checks.append({
            "id": node,
            "weights_match_lean": True,
            "dbm_entries_checked": 100,
            "min_row_cap_slack": str(min(slacks)),
            "strict_margin": str(required - upper),
            "lean_module_sha256": sha256(path),
        })

    result = {
        "scope": "source-level exact-rational bridge audit; not a kernel verdict or payment",
        "certificate_sha256": sha256(CERT),
        "rational_core_sha256": sha256(CORE),
        "frozen_dbm_sha256": sha256(common.DBM),
        "records_checked": len(checks),
        "dual_weights_checked": 9 * len(checks),
        "dbm_entries_checked": 100 * len(checks),
        "row_caps_checked": 100 * len(checks),
        "checks": checks,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2))


if __name__ == "__main__":
    main()
