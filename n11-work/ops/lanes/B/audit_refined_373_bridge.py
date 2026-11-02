#!/usr/bin/env python3
"""Audit the exact 389 -> 373 residual bridge independently of Lean.

This parses the frozen terminal flags, the old 389-id census, the sixteen
newly removed ids, and the 120 sharp ids. It checks the exact set identity
``refined = old389 \\ removed16`` together with cardinality and terminal/sharp
membership. It is a source-and-set audit, not Lean elaboration or proof credit.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"

SOURCE_TREE = LEAN / "DBMSourceTreeData.lean"
OLD_CENSUS = LEAN / "EnergyTerminalResidualCensusBase.lean"
RESIDUAL_CARD = LEAN / "EnergyTerminalBatchB13RefineSixteenResidualCard.lean"
SHARP = LEAN / "Patch120DomainPacket.lean"
REPORT = LANE / "audit_refined_373_bridge-report.json"
RESIDUAL_LIST = LANE / "residual373-ids.txt"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def terminal_ids() -> set[int]:
    text = SOURCE_TREE.read_text(encoding="utf-8")
    pat = re.compile(
        r"def node(\d+) : Node 5011 where(.*?)"
        r"(?=\ndef node\d+ : Node 5011 where|\ndef data)",
        re.S,
    )
    return {int(m.group(1)) for m in pat.finditer(text) if "terminal := true" in m.group(2)}


def finset_literal(path: Path, name: str) -> set[int]:
    text = path.read_text(encoding="utf-8")
    match = re.search(
        rf"^def {re.escape(name)}\s*:\s*Finset \(Fin 5011\)\s*:=\s*\{{([^}}]*)\}}",
        text,
        re.MULTILINE,
    )
    if match is None:
        raise SystemExit(f"missing literal {name} in {path.name}")
    return {int(value) for value in re.findall(r"\d+", match.group(1))}


def patch_ids() -> set[int]:
    text = SHARP.read_text(encoding="utf-8")
    match = re.search(
        r"def patchID\s*:\s*Fin 120\s*→\s*Fin 5011\s*:=\s*!\[([^\]]*)\]",
        text,
        re.DOTALL,
    )
    if match is None:
        raise SystemExit("missing patchID literal")
    return {int(value) for value in re.findall(r"\d+", match.group(1))}


def main() -> int:
    terminals = terminal_ids()
    old389 = set().union(
        *(finset_literal(OLD_CENSUS, f"chunk{index}") for index in range(4))
    )
    removed = finset_literal(RESIDUAL_CARD, "removedIDs")
    sharp = patch_ids()
    refined = old389 - removed
    residual_text = RESIDUAL_CARD.read_text(encoding="utf-8")
    residual_list_bytes = "".join(f"{value}\n" for value in sorted(refined)).encode()
    RESIDUAL_LIST.write_bytes(residual_list_bytes)

    checks = {
        "source_terminal_count_2506": len(terminals) == 2506,
        "old_census_count_389": len(old389) == 389,
        "old_census_all_terminal": old389 <= terminals,
        "removed_count_16": len(removed) == 16,
        "removed_all_subset_old_census": removed <= old389,
        "removed_all_terminal": removed <= terminals,
        "removed_none_sharp": removed.isdisjoint(sharp),
        "sharp_count_120": len(sharp) == 120,
        "refined_exact_difference": refined == old389 - removed,
        "refined_count_373": len(refined) == 373,
        "refined_all_terminal": refined <= terminals,
        "refined_none_sharp": refined.isdisjoint(sharp),
        "refined_card_claimed_373": "theorem residualIDs_card : residualIDs.card = 373" in residual_text,
        "terminal_census_claimed_2506": "theorem terminalIDs_card : terminalIDs.card = 2506" in (
            LEAN / "EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean"
        ).read_text(encoding="utf-8"),
    }
    failed = [name for name, passed in checks.items() if not passed]
    report = {
        "ok": not failed,
        "scope": "exact source-ID set/cardinality audit; not Lean elaboration or kernel proof credit",
        "counts": {
            "source_terminals": len(terminals),
            "sharp": len(sharp),
            "old_residual": len(old389),
            "removed": len(removed),
            "refined_residual": len(refined),
        },
        "removed_ids": sorted(removed),
        "refined_ids_sha256": hashlib.sha256(
            ",".join(map(str, sorted(refined))).encode()
        ).hexdigest().upper(),
        "residual_list_file": RESIDUAL_LIST.name,
        "residual_list_sha256": hashlib.sha256(residual_list_bytes).hexdigest().upper(),
        "checks": checks,
        "source_sha256": {
            path.name: sha256(path)
            for path in (SOURCE_TREE, OLD_CENSUS, RESIDUAL_CARD, SHARP)
        },
    }
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
