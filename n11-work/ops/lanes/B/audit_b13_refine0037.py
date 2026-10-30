#!/usr/bin/env python3
"""Audit the source facts behind EnergyTerminalBatchB13Refine0037."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[4]
LEAN = REPO / "n11-work" / "lean" / "N11Formalization"
REFINE = LEAN / "EnergyTerminalBatchB13Refine0037.lean"
NEXT505 = LEAN / "Paid16GeneralNext505.lean"
TARGETS = Path(__file__).with_name("TARGETS.txt")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> int:
    refine = REFINE.read_text()
    next505 = NEXT505.read_text()
    targets = [
        line.strip()
        for line in TARGETS.read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    failures: list[str] = []

    blocks: list[list[int]] = []
    for index in range(25):
        match = re.search(
            rf"^def ids{index:02d} : Finset \(Fin 5011\) := \{{([^}}]*)\}}$",
            next505,
            re.MULTILINE,
        )
        if match is None:
            failures.append(f"missing ids{index:02d}")
            continue
        blocks.append([int(value) for value in re.findall(r"\d+", match.group(1))])

    flattened = [value for block in blocks for value in block]
    expected_parts = [f"ids{index:02d}" for index in range(25)]
    new_mem_match = re.search(
        r"^theorem new_mem \(n : Fin 5011\) : n ∈ newIDs ↔ (.*)$",
        next505,
        re.MULTILINE,
    )
    new_mem_parts = (
        re.findall(r"n ∈ (ids\d{2})", new_mem_match.group(1))
        if new_mem_match is not None
        else []
    )
    checks = {
        "next505_block_count": len(blocks),
        "next505_total_ids": len(flattened),
        "next505_unique_ids": len(set(flattened)),
        "next505_contains_37": 37 in flattened,
        "next505_min_id": min(flattened) if flattened else None,
        "new_mem_part_count": len(new_mem_parts),
        "new_mem_parts_exact": new_mem_parts == expected_parts,
        "refine0037_target_count": targets.count(
            "N11Formalization.EnergyTerminalBatchB13Refine0037"
        ),
        "refine_twelve_target_count": targets.count(
            "N11Formalization.EnergyTerminalBatchB13RefineTwelve"
        ),
        "refine0037_precedes_twelve": (
            "N11Formalization.EnergyTerminalBatchB13Refine0037" in targets
            and "N11Formalization.EnergyTerminalBatchB13RefineTwelve" in targets
            and targets.index("N11Formalization.EnergyTerminalBatchB13Refine0037")
            < targets.index("N11Formalization.EnergyTerminalBatchB13RefineTwelve")
        ),
        "refine_sha256": digest(REFINE),
        "next505_sha256": digest(NEXT505),
    }
    if len(blocks) != 25:
        failures.append("expected 25 Next505 literal blocks")
    if len(flattened) != 505:
        failures.append("expected 505 Next505 literal ids")
    if len(set(flattened)) != len(flattened):
        failures.append("duplicate id within Next505 literal blocks")
    if 37 in flattened:
        failures.append("id 37 occurs in Next505 and cannot be excluded")
    if new_mem_parts != expected_parts:
        failures.append("new_mem does not list exactly ids00 through ids24 in order")
    if targets.count("N11Formalization.EnergyTerminalBatchB13Refine0037") != 1:
        failures.append("Refine0037 must occur exactly once in TARGETS.txt")
    if targets.count("N11Formalization.EnergyTerminalBatchB13RefineTwelve") != 1:
        failures.append("RefineTwelve must occur exactly once in TARGETS.txt")
    if "N11Formalization.EnergyTerminalBatchB13Refine0037" in targets and \
            "N11Formalization.EnergyTerminalBatchB13RefineTwelve" in targets and \
            targets.index("N11Formalization.EnergyTerminalBatchB13Refine0037") > \
            targets.index("N11Formalization.EnergyTerminalBatchB13RefineTwelve"):
        failures.append("Refine0037 must precede RefineTwelve in TARGETS.txt")

    exclusion = re.search(
        r"private theorem not_next505 :\n(.*?)\n\ntheorem not_paid_0037",
        refine,
        re.DOTALL,
    )
    if exclusion is None:
        failures.append("missing not_next505 theorem")
    else:
        body = exclusion.group(1)
        required = (
            "Paid16GeneralNext505.newIDs",
            "rw [Paid16GeneralNext505.new_mem]",
            "push_neg",
            "repeat' constructor <;> decide +kernel",
        )
        for fragment in required:
            if fragment not in body:
                failures.append(f"not_next505 lacks {fragment!r}")
        if "next505_lt" in body:
            failures.append("not_next505 still uses the invalid lower-bound argument")

    if "exact not_next505 h505" not in refine:
        failures.append("not_paid_0037 does not invoke not_next505")
    for banned in ("sorry", "admit", "native_decide", "maxHeartbeats 0"):
        if banned in refine:
            failures.append(f"banned token in refine0037: {banned}")

    print(json.dumps({"ok": not failures, "checks": checks, "failed": failures}, indent=2))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
