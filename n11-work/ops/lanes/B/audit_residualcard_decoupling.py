#!/usr/bin/env python3
"""Audit that the B13 ResidualCard bridge avoids the old 389-id census."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
CARD = LEAN / "EnergyTerminalBatchB13RefineSixteenResidualCard.lean"
SHARP = LEAN / "Patch120DomainPacket.lean"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def closure(root: str) -> set[str]:
    seen: set[str] = set()
    stack = [root]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        path = LEAN / f"{module.rsplit('.', 1)[-1]}.lean"
        if not path.exists():
            continue
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("import N11Formalization."):
                stack.append(line.split()[1])
    return seen


def main() -> None:
    text = CARD.read_text(encoding="utf-8")
    removed_match = re.search(r"def removedIDs : Finset \(Fin 5011\) :=\s*\{(.*?)\}", text, re.S)
    removed = [int(x) for x in re.findall(r"\d+", removed_match.group(1))] if removed_match else []
    patch_match = re.search(r"def patchID : Fin 120 → Fin 5011 :=\s*!\[(.*?)\]", SHARP.read_text(encoding="utf-8"), re.S)
    patches = [int(x) for x in re.findall(r"\d+", patch_match.group(1))] if patch_match else []
    modules = closure("N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCard")
    old_census = {
        "N11Formalization.EnergyTerminalResidualCensus",
        "N11Formalization.EnergyTerminalResidualCensusC01",
        "N11Formalization.EnergyTerminalResidualCensusC02",
        "N11Formalization.EnergyTerminalResidualCensusC03",
        "N11Formalization.EnergyTerminalResidualCensusC04",
        "N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff",
    }
    checks = {
        "sixteen_removed_ids": len(removed) == 16 and len(set(removed)) == 16,
        "removed_ids_disjoint_from_120_sharp_ids": bool(patch_match) and len(patches) == 120 and not (set(removed) & set(patches)),
        "old_census_absent_from_closure": not (old_census & modules),
        "terminal_census_present": "N11Formalization.EnergyTerminalBatchB13RefineSixteenTerminalCensus" in modules,
        "census_sdiff_import_absent": "EnergyTerminalBatchB13RefineSixteenResidualCensusSdiff" not in text,
        "forbidden_tokens_absent": not re.search(r"\b(sorry|admit|native_decide|implemented_by)\b", text),
    }
    report = {
        "ok": all(checks.values()),
        "checks": checks,
        "removed_count": len(removed),
        "sharp_count": len(patches),
        "closure_size": len(modules),
        "scope": "source/import and literal-id audit only; not Lean elaboration or kernel checking",
        "sha256": {
            "ResidualCard.lean": digest(CARD),
            "Patch120DomainPacket.lean": digest(SHARP),
        },
    }
    out = HERE / "audit_residualcard_decoupling-report.json"
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
