#!/usr/bin/env python3
"""Audit an archived EnergyRefine tree by exact integer DBM checks."""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common


def parse_nodes(text):
    count = int(re.search(r"abbrev K := (\d+)", text).group(1))
    nodes = {}
    for node in range(count):
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
        nodes[node] = {"matrix": matrix, "meta": meta}
    return count, nodes


def audit(source, node_id, frozen_source):
    text = source.read_text(encoding="utf-8")
    count, nodes = parse_nodes(text)
    frozen = common.parse_db(frozen_source.read_text(encoding="utf-8"), node_id)
    scale_bad = [(i, j, nodes[0]["matrix"][i][j], 256 * frozen[i][j])
                 for i in range(10) for j in range(10)
                 if nodes[0]["matrix"][i][j] != 256 * frozen[i][j]]
    split_bad = []
    checked = 0
    for node, data in nodes.items():
        terminal, i, j, m, left, right = data["meta"]
        if terminal:
            continue
        if left not in nodes or right not in nodes:
            split_bad.append([node, "missing child", left, right])
            continue
        for a in range(10):
            for b in range(10):
                lm = min(data["matrix"][a][b], data["matrix"][a][i] + m + data["matrix"][j][b])
                rm = min(data["matrix"][a][b], data["matrix"][a][j] - m + data["matrix"][i][b])
                checked += 2
                if lm > nodes[left]["matrix"][a][b] or rm > nodes[right]["matrix"][a][b]:
                    split_bad.append([node, a, b, lm, nodes[left]["matrix"][a][b],
                                      rm, nodes[right]["matrix"][a][b]])
    leaves = [node for node, data in nodes.items() if data["meta"][0]]
    report = {
        "scope": "exact integer tree data only; no MPacket, Lean build or kernel credit",
        "source_id": node_id,
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "frozen_source_sha256": hashlib.sha256(frozen_source.read_bytes()).hexdigest(),
        "node_count": count,
        "terminal_nodes": leaves,
        "root_scale_entries_checked": 100,
        "root_scale_mismatches": scale_bad,
        "split_entries_checked": checked,
        "split_violations": split_bad,
        "passed": not scale_bad and not split_bad,
    }
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("node_id", type=int)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    frozen = ROOT / "n11-work/lean/N11Formalization/DBMSourceTreeData.lean"
    report = audit(args.source, args.node_id, frozen)
    rendered = json.dumps(report, indent=2) + "\n"
    if args.out:
        args.out.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    raise SystemExit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
