#!/usr/bin/env python3
"""Audit the literal sixteen-id delta used by the ResidualCard bridge.

This reconstructs the refinement chain from the Lean sources and checks the
exact set equality `Repair.paidIDs = B13.paidIDs union removedIDs`.  It is a
static source check, not Lean elaboration or kernel proof credit.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"

CHAIN = {
    "EnergyTerminalBatchB13RefineSeven": [
        "EnergyRefineN2341", "EnergyRefineN3040", "EnergyRefineN2965",
        "EnergyRefineN3440", "EnergyRefineN3589", "EnergyRefineN3623",
        "EnergyRefineN3633",
    ],
    "EnergyTerminalBatchB13RefineEight": [
        "EnergyTerminalBatchB13RefineSeven", "EnergyRefineN2337",
    ],
    "EnergyTerminalBatchB13RefineEleven": [
        "EnergyTerminalBatchB13RefineEight", "EnergyRefineN3777",
        "EnergyRefineN3792", "EnergyRefineN3853",
    ],
    "EnergyTerminalBatchB13RefineTwelve": [
        "EnergyTerminalBatchB13RefineEleven", "EnergyRefineN0037",
    ],
    "EnergyTerminalBatchB13RefineThirteen": [
        "EnergyTerminalBatchB13RefineTwelve", "EnergyRefineN3112",
    ],
    "EnergyTerminalBatchB13RefineFourteen": [
        "EnergyRefineN3116",
    ],
    "EnergyTerminalBatchB13RefineSixteenRepair": [
        "EnergyRefineN3431", "EnergyRefineN3573",
    ],
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def singleton_ids(module: str) -> set[int]:
    text = (LEAN / f"{module}.lean").read_text(encoding="utf-8")
    match = re.search(r"def newIDs : Finset \(Fin 5011\) :=\s*\{(\d+)\}", text)
    if not match:
        raise ValueError(f"missing literal newIDs in {module}")
    return {int(match.group(1))}


def chain_delta() -> tuple[set[int], dict[str, int]]:
    delta: set[int] = set()
    sizes: dict[str, int] = {}
    for module, inputs in CHAIN.items():
        source = (LEAN / f"{module}.lean").read_text(encoding="utf-8")
        body_match = re.search(
            r"def newIDs : Finset \(Fin 5011\) :=\s*(.*?)\n\ndef paidIDs", source, re.S
        )
        if not body_match:
            raise ValueError(f"missing newIDs body in {module}")
        body = body_match.group(1)
        cited = set(re.findall(r"([A-Za-z0-9]+)\.newIDs", body))
        if cited != set(inputs):
            raise ValueError(f"{module}: cited {sorted(cited)} != expected {sorted(inputs)}")
        fresh: set[int] = set()
        for item in inputs:
            fresh |= singleton_ids(item) if item.startswith("EnergyRefineN") else set()
        if len(fresh) != sum(len(singleton_ids(x)) for x in inputs if x.startswith("EnergyRefineN")):
            raise ValueError(f"{module}: duplicate singleton source ids")
        delta |= fresh
        sizes[module] = len(fresh)
    return delta, sizes


def main() -> None:
    card = LEAN / "EnergyTerminalBatchB13RefineSixteenResidualCard.lean"
    text = card.read_text(encoding="utf-8")
    removed_match = re.search(
        r"def removedIDs : Finset \(Fin 5011\) :=\s*\{(.*?)\}", text, re.S
    )
    removed = {int(x) for x in re.findall(r"\d+", removed_match.group(1))}
    delta, sizes = chain_delta()
    repair = (LEAN / "EnergyTerminalBatchB13RefineSixteenRepair.lean").read_text(encoding="utf-8")
    checks = {
        "sixteen_literal_ids": len(removed) == 16,
        "chain_delta_equals_literal": delta == removed,
        "chain_delta_count_16": len(delta) == 16,
        "base_plus_delta_2013": 1997 + len(delta) == 2013,
        "repair_paid_count_2013": bool(re.search(r"theorem paid_count : paidIDs\.card = 2013", repair)),
        "equality_theorem_present": "paidIDs_eq_base_union_removed" in text,
        "forbidden_tokens_absent": not re.search(r"\b(sorry|admit|native_decide|implemented_by)\b", text),
    }
    report = {
        "ok": all(checks.values()),
        "checks": checks,
        "delta_ids": sorted(delta),
        "delta_by_module": sizes,
        "scope": "static reconstruction from Lean source definitions; not Lean elaboration or kernel checking",
        "sha256": {
            p.name: digest(p) for p in [
                card,
                LEAN / "EnergyTerminalBatchB13RefineSixteenRepair.lean",
                LEAN / "EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean",
            ]
        },
    }
    out = HERE / "audit_paid_delta-report.json"
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
