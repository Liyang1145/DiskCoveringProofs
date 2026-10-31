#!/usr/bin/env python3
"""Static audit of the lane-B Fourteen refinement handoff.

This checks source structure, exact handoff arithmetic, target ordering, and
banned proof escapes.  It does not elaborate Lean and is not proof credit.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LANE = Path(__file__).resolve().parent
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
REFINE = LEAN / "EnergyTerminalBatchB13RefineFourteen.lean"
MAIN = LEAN / "EnergyTerminalBatchB13RefineFourteenMain.lean"
TARGETS = LANE / "TARGETS.txt"
REPORT = LANE / "audit_b13_refine_fourteen-report.json"

REFINE_TARGET = "N11Formalization.EnergyTerminalBatchB13RefineFourteen"
MAIN_TARGET = "N11Formalization.EnergyTerminalBatchB13RefineFourteenMain"
BANNED = (
    "sorry",
    "admit",
    "native_decide",
    "ofReduceBool",
    "implemented_by",
    "maxHeartbeats 0",
    "maxRecDepth",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    refine = REFINE.read_text()
    wrapper = MAIN.read_text()
    targets = [line.strip() for line in TARGETS.read_text().splitlines() if line.strip()]
    checks: dict[str, bool] = {}

    checks["refine_exists"] = REFINE.is_file()
    checks["main_exists"] = MAIN.is_file()
    checks["refine_imports_thirteen"] = (
        "import N11Formalization.EnergyTerminalBatchB13RefineThirteen" in refine
    )
    checks["refine_imports_3116"] = (
        "import N11Formalization.EnergyTerminalBatchB13Refine3116" in refine
    )
    checks["main_imports_b13main"] = (
        "import N11Formalization.EnergyTerminalBatchB13Main" in wrapper
    )
    checks["main_imports_fourteen"] = (
        "import N11Formalization.EnergyTerminalBatchB13RefineFourteen" in wrapper
    )
    checks["paid_base_is_thirteen"] = (
        "EnergyTerminalBatchB13RefineThirteen.paidIDs ∪ newIDs" in refine
        and "EnergyTerminalBatchB13RefineThirteen.paidIDs ∪ "
        "EnergyRefineN3116.newIDs" not in refine
    )
    checks["new_ids_is_3116"] = "def newIDs : Finset (Fin 5011) := EnergyRefineN3116.newIDs" in refine
    checks["paid_count_2011"] = "theorem paid_count : paidIDs.card = 2011" in refine
    checks["new_count_1"] = "theorem new_count : newIDs.card = 1" in refine
    checks["paid_count_uses_alias_count"] = (
        "rw [paidIDs, newIDs, Finset.card_union_of_disjoint new_disjoint_old," in refine
        and "EnergyTerminalBatchB13RefineThirteen.paid_count," in refine
        and "EnergyTerminalBatchB13Refine3116.new_count]" in refine
    )
    checks["residual_375_documented"] = "2011 ids, leaving 376 - 1 = 375" in refine
    checks["paid_radius_present"] = "theorem paid_radius" in refine
    checks["remaining_transfer_present"] = (
        "theorem remaining_of (h : RemainingTerminalRadius) :\n"
        "    EnergyTerminalBatchB13.RemainingTerminalRadius" in refine
    )
    checks["main_consumer_present"] = (
        "main_of_energy_refineFourteen_and_seven_classes" in wrapper
        and "full_disk_bound_of_energy_refineFourteen_and_seven_classes" in wrapper
    )
    checks["no_banned_refine"] = not any(token in refine for token in BANNED)
    checks["no_banned_main"] = not any(token in wrapper for token in BANNED)
    checks["refine_target_once"] = targets.count(REFINE_TARGET) == 1
    checks["main_target_once"] = targets.count(MAIN_TARGET) == 1
    checks["target_order"] = (
        checks["refine_target_once"]
        and checks["main_target_once"]
        and targets.index(REFINE_TARGET) < targets.index(MAIN_TARGET)
    )

    result = {
        "ok": all(checks.values()),
        "scope": "static source/inventory only; no Lean elaboration or proof credit",
        "checks": checks,
        "handoff": {
            "paid_before": 2010,
            "new_ids": [3116],
            "paid_after": 2011,
            "residual_before": 376,
            "residual_after": 375,
        },
        "sha256": {
            "refine": sha256(REFINE),
            "main": sha256(MAIN),
            "targets": sha256(TARGETS),
            "dependency_3116": sha256(LEAN / "EnergyRefineN3116.lean"),
            "wrapper_3116": sha256(LEAN / "EnergyTerminalBatchB13Refine3116.lean"),
            "dependency_thirteen": sha256(LEAN / "EnergyTerminalBatchB13RefineThirteen.lean"),
        },
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
