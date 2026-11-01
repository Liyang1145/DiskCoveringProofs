#!/usr/bin/env python3
"""Check that peak-max projections are definitional, not kernel-decided.

The q0 peak tables already store the exact maximum literals.  Re-proving each
vector projection with ``decide +kernel`` forced the kernel to compare enormous
rationals and caused the first uncached lane-A CI target to exhaust memory.
This checker verifies that every projection rewrite uses ``rfl`` and repeats the
corresponding literal from ``SevenClassQ0Deg3UpperTables`` byte-for-byte.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
TABLES = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperTables.lean"
EDGE = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperReductionUnimodal.lean"
SECTOR = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3SectorPeak.lean"


def array_literals(text: str, declaration: str, count: int) -> list[str]:
    match = re.search(
        rf"def {declaration} : Fin {count} → ℚ := !\[(.*?)\n\]", text, re.S
    )
    if match is None:
        raise ValueError(f"missing {declaration}")
    values = [item.strip().strip("()") for item in match.group(1).strip().split(",")]
    if len(values) != count:
        raise ValueError(f"{declaration}: expected {count} values, got {len(values)}")
    return values


def check(
    text: str,
    definition: str,
    projection: str,
    expected: list[str],
) -> list[str]:
    matches = re.findall(
        rf"show {projection} (\d+) = \((.*?)\) by (rfl|decide \+kernel)", text, re.S
    )
    failures: list[str] = []
    if [int(index) for index, _, _ in matches] != list(range(len(expected))):
        failures.append(f"{definition}: expected ordered indices 0..{len(expected) - 1}")
    for index_text, literal, tactic in matches:
        index = int(index_text)
        if tactic != "rfl":
            failures.append(f"{definition} {index}: max projection is not definitional")
        if index < len(expected) and literal != expected[index]:
            failures.append(f"{definition} {index}: rewrite literal differs from table")
    return failures


def main() -> int:
    tables = TABLES.read_text(encoding="utf-8")
    failures = check(
        EDGE.read_text(encoding="utf-8"),
        "edgeMaxAt",
        "edgeMaxAt",
        array_literals(tables, "edgeMaxAt", 21),
    )
    failures += check(
        SECTOR.read_text(encoding="utf-8"),
        "sectorMax",
        "sectorMax",
        array_literals(tables, "sectorMax", 9),
    )
    if failures:
        print("FAIL")
        print("\n".join(failures))
        return 1
    print("PASS: 21 edge and 9 sector max projections are exact rfl rewrites")
    return 0


if __name__ == "__main__":
    sys.exit(main())
