#!/usr/bin/env python3
"""Static audit of the unique Seven -> Eight -> Eleven -> ... -> Sixteen chain.

This catches duplicate certificate aggregation and checks the exact handoff
arithmetic.  It does not elaborate Lean and is not proof credit.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LANE = Path(__file__).resolve().parent
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
TARGETS = LANE / "TARGETS.txt"
REPORT = LANE / "audit_b13_refine_sixteen-report.json"

CHAIN = ("Seven", "Eight", "Eleven", "Twelve", "Thirteen", "Fourteen", "Sixteen")
TARGET_CHAIN = ("Fourteen", "Sixteen")
INCREMENTS = (7, 1, 3, 1, 1, 1, 2)
EXPECTED_IDS = (
    "0037", "2337", "2341", "2965", "3040", "3112", "3116", "3431",
    "3440", "3573", "3589", "3623", "3633", "3777", "3792", "3853",
)
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0", "maxRecDepth")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source(name: str, main: bool = False) -> tuple[Path, str]:
    suffix = "Main" if main else ""
    path = LEAN / f"EnergyTerminalBatchB13Refine{name}{suffix}.lean"
    return path, path.read_text()


def main() -> int:
    targets = [line.strip() for line in TARGETS.read_text().splitlines() if line.strip()]
    sources = {name: source(name) for name in CHAIN}
    mains = {name: source(name, main=True) for name in CHAIN}
    sixteen = sources["Sixteen"][1]
    main16 = mains["Sixteen"][1]
    checks: dict[str, bool] = {}
    checks["all_sources_exist"] = all(
        path.is_file() for path, _ in (*sources.values(), *mains.values())
    )
    checks["increment_sum"] = sum(INCREMENTS) == 16
    checks["final_arithmetic"] = (
        "theorem paid_count : paidIDs.card = 2013" in sixteen
        and "theorem new_count : newIDs.card = 2" in sixteen
        and re.search(r"2011 to 2013,\s+leaving 389 - 16 = 373", sixteen) is not None
    )
    checks["sixteen_new_count_uses_singleton_counts"] = (
        "theorem new_disjoint_parts :\n"
        "    Disjoint EnergyRefineN3431.newIDs EnergyRefineN3573.newIDs" in sixteen
        and "Finset.card_union_of_disjoint new_disjoint_parts" in sixteen
        and "EnergyTerminalBatchB13Refine3431.new_count" in sixteen
        and "EnergyTerminalBatchB13Refine3573.new_count" in sixteen
        and "theorem new_count : newIDs.card = 2 := by\n  decide +kernel" not in sixteen
    )
    thirteen = sources["Thirteen"][1]
    fourteen = sources["Fourteen"][1]
    checks["thirteen_close_has_no_redundant_tactic"] = (
        "theorem twelve_new_count :" in thirteen
        and "EnergyTerminalBatchB13RefineTwelve.new_count]" in thirteen
        and "EnergyTerminalBatchB13RefineTwelve.new_count]\n    norm_num" not in thirteen
    )
    expected_paid = dict(zip(CHAIN, (2004, 2005, 2008, 2009, 2010, 2011, 2013)))
    checks["all_stage_paid_counts"] = all(
        f"theorem paid_count : paidIDs.card = {count}" in sources[name][1]
        for name, count in expected_paid.items()
    )
    checks["fourteen_paid_ids_use_alias"] = (
        "EnergyTerminalBatchB13RefineThirteen.paidIDs ∪ newIDs" in fourteen
        and "EnergyTerminalBatchB13RefineThirteen.paidIDs ∪ EnergyRefineN3116.newIDs" not in fourteen
    )
    checks["sixteen_imports"] = all(
        f"import N11Formalization.EnergyTerminalBatchB13Refine{i}" in sixteen
        for i in ("Fourteen", "3431", "3573")
    )
    checks["no_duplicate_aggregate"] = (
        "EnergyTerminalBatchB13RefineTwentyTwo" not in sixteen
        and "EnergyTerminalBatchB13RefineTwentyFour" not in sixteen
        and "EnergyTerminalBatchB13RefineFourteen.paidIDs ∪ newIDs" in sixteen
    )
    checks["sixteen_ids"] = (
        "EnergyRefineN3431.newIDs ∪ EnergyRefineN3573.newIDs" in sixteen
        and sixteen.count(".new_radius n hn") == 2
        and sixteen.count(".new_terminal n hn") == 2
    )
    checks["all_singleton_ids_reachable"] = all(
        any(f"EnergyRefineN{i}.newIDs" in text for _, text in sources.values())
        for i in EXPECTED_IDS
    )
    checks["unique_id_count"] = len(set(EXPECTED_IDS)) == 16
    checks["remaining_transfer"] = (
        "EnergyTerminalBatchB13.RemainingTerminalRadius" in sixteen
        and "theorem remaining_of (h : RemainingTerminalRadius) :" in sixteen
    )
    checks["main_consumers"] = (
        "main_of_energy_refineSixteen_and_seven_classes" in main16
        and "full_disk_bound_of_energy_refineSixteen_and_seven_classes" in main16
    )
    checks["no_banned_sources"] = all(
        not any(token in text for token in BANNED)
        for _, text in (*sources.values(), *mains.values())
    )
    checks["targets_once"] = all(
        targets.count(f"N11Formalization.EnergyTerminalBatchB13Refine{name}{suffix}") == 1
        for name in TARGET_CHAIN for suffix in ("", "Main")
    )
    checks["stale_targets_absent"] = not any(
        f"Refine{name}" in target for name in ("TwentyTwo", "TwentyFour")
        for target in targets
    )
    checks["target_order"] = checks["targets_once"] and all(
        targets.index(f"N11Formalization.EnergyTerminalBatchB13Refine{name}") <
        targets.index(f"N11Formalization.EnergyTerminalBatchB13Refine{name}Main")
        for name in TARGET_CHAIN
    ) and all(
        targets.index(f"N11Formalization.EnergyTerminalBatchB13Refine{a}Main") <
        targets.index(f"N11Formalization.EnergyTerminalBatchB13Refine{b}")
        for a, b in zip(TARGET_CHAIN, TARGET_CHAIN[1:])
    )
    result = {
        "ok": all(checks.values()),
        "scope": "static source/inventory and duplicate-ID arithmetic; no Lean elaboration",
        "checks": checks,
        "handoff": {
            "paid_before": 1997,
            "paid_after": 2013,
            "new_refinements": 16,
            "residual_before": 389,
            "residual_after": 373,
            "increments": dict(zip(CHAIN, INCREMENTS)),
        },
        "sha256": {
            "targets": sha256(TARGETS),
            **{f"{name.lower()}_refine": sha256(sources[name][0]) for name in CHAIN},
            **{f"{name.lower()}_main": sha256(mains[name][0]) for name in CHAIN},
        },
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
