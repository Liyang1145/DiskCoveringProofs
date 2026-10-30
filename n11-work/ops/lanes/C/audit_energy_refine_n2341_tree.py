#!/usr/bin/env python3
"""Exact audit of the restored N2341 refinement tree data.

This checks only the 3-node DBM split/scale layer. It does not check MPacket
fields and is not a Lean or kernel verdict.
"""
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
REFINE = LEAN / "EnergyRefineN2341.lean"
SOURCE = LEAN / "DBMSourceTreeData.lean"
OUT = HERE / "energy-refine-n2341-tree-audit.json"


def nodes():
    text = REFINE.read_text()
    result = {}
    for node in range(3):
        start = text.index(f"def node{node} :")
        end = text.index("\ndef ", start + 1)
        line = text[start:end]
        rows = re.findall(r"!\[((?:-?\d+,){9}-?\d+)\]", line)
        if len(rows) != 10:
            raise ValueError(f"node{node}: expected 10 matrix rows, got {len(rows)}")
        matrix = [[int(x) for x in row.split(",")] for row in rows[:10]]
        match = re.search(r"\]\],\s*([^⟩]+)⟩", line)
        if not match:
            raise ValueError(f"node{node}: metadata not found")
        meta = [x.strip() == "true" if x.strip() in ("true", "false")
                else int(x.strip()) for x in match.group(1).split(",")]
        if len(meta) != 6:
            raise ValueError(f"node{node}: expected 6 metadata fields, got {meta}")
        result[node] = {"matrix": matrix, "meta": meta}
    return result


def main():
    ns = nodes()
    frozen = common.parse_db(SOURCE.read_text(), 2341)
    scale_bad = [(i, j, ns[0]["matrix"][i][j], 256 * frozen[i][j])
                 for i in range(10) for j in range(10)
                 if ns[0]["matrix"][i][j] != 256 * frozen[i][j]]

    root = ns[0]
    terminal, i, j, m, left, right = root["meta"]
    split_bad = []
    for a in range(10):
        for b in range(10):
            lm = min(root["matrix"][a][b], root["matrix"][a][i] + m + root["matrix"][j][b])
            rm = min(root["matrix"][a][b], root["matrix"][a][j] - m + root["matrix"][i][b])
            if lm > ns[left]["matrix"][a][b] or rm > ns[right]["matrix"][a][b]:
                split_bad.append([a, b, lm, ns[left]["matrix"][a][b], rm, ns[right]["matrix"][a][b]])

    child_terminal = {n: bool(ns[n]["meta"][0]) for n in (1, 2)}
    report = {
        "scope": "exact integer tree data only; no MPacket, Lean build or kernel credit",
        "refine_sha256": hashlib.sha256(REFINE.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "root_scale_entries_checked": 100,
        "root_scale_mismatches": scale_bad,
        "root_metadata": {"terminal": terminal, "i": i, "j": j, "m": m,
                          "left": left, "right": right},
        "split_entries_checked": 200,
        "split_violations": split_bad,
        "child_terminal": child_terminal,
        "passed": not scale_bad and not split_bad and terminal == 0
                  and left == 1 and right == 2 and all(child_terminal.values()),
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
