#!/usr/bin/env python3
"""Static preflight for replacing the root's B12Main import with ThirteenMain.

This checks the exact one-line handoff and its source/API prerequisites.  It is
not Lean elaboration, a CI verdict, or proof credit for any residual terminal.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work" / "lean"
ROOT_MODULE = LEAN / "N11Formalization.lean"
MAIN = LEAN / "N11Formalization" / "EnergyTerminalBatchB13RefineThirteenMain.lean"
THIRTEEN = LEAN / "N11Formalization" / "EnergyTerminalBatchB13RefineThirteen.lean"
TARGETS = LANE / "TARGETS.txt"
REPORT = LANE / "audit_thirteen_root_switch-report.json"

OLD = "import N11Formalization.EnergyTerminalBatchB12Main"
NEW = "import N11Formalization.EnergyTerminalBatchB13RefineThirteenMain"
REQUIRED_IMPORTS = {
    "import N11Formalization.EnergyTerminalBatchB13Main",
    "import N11Formalization.EnergyTerminalBatchB13RefineThirteen",
}
REQUIRED_NAMES = {
    "main_of_energy_refineThirteen_and_seven_classes",
    "full_disk_bound_of_energy_refineThirteen_and_seven_classes",
}
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0", "maxRecDepth")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def root_phase(text: str) -> tuple[str, int, int]:
    lines = text.splitlines()
    old_count, new_count = lines.count(OLD), lines.count(NEW)
    if old_count == 1 and new_count == 0:
        return "pre_handoff", old_count, new_count
    if old_count == 0 and new_count == 1:
        return "post_handoff", old_count, new_count
    return "invalid", old_count, new_count


def main() -> None:
    root_text = ROOT_MODULE.read_text(encoding="utf-8")
    main_text = MAIN.read_text(encoding="utf-8")
    thirteen_text = THIRTEEN.read_text(encoding="utf-8")
    targets = [line.strip() for line in TARGETS.read_text(encoding="utf-8").splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    phase, old_count, new_count = root_phase(root_text)
    banned = {token: bool(re.search(r"(?<![\w.])" + re.escape(token) + r"(?![\w])",
                                    main_text + "\n" + thirteen_text))
              for token in BANNED}
    new_target = NEW.removeprefix("import ")
    prereq_targets = (
        "N11Formalization.EnergyTerminalBatchB13Main",
        "N11Formalization.EnergyTerminalBatchB13RefineThirteen",
    )
    checks = {
        "root_has_exactly_one_valid_import": phase != "invalid",
        "required_transitive_imports_present": all(
            line in main_text.splitlines() for line in REQUIRED_IMPORTS),
        "consumer_api_present": all(name in main_text for name in REQUIRED_NAMES),
        "remaining_of_bridge_present": "EnergyTerminalBatchB13RefineThirteen.remaining_of henergy" in main_text,
        "no_banned_tokens": not any(banned.values()),
        "new_main_in_targets_once": targets.count(new_target) == 1,
        "prerequisites_in_targets_once": all(targets.count(t) == 1 for t in prereq_targets),
        "target_order_main_after_prerequisites": new_target in targets and all(
            t in targets and targets.index(t) < targets.index(new_target) for t in prereq_targets),
    }
    report = {
        "scope": "static one-line root/import/API preflight only; no Lean elaboration or proof credit",
        "root_import_phase": phase,
        "old_import": OLD,
        "new_import": NEW,
        "old_import_count": old_count,
        "new_import_count": new_count,
        "checks": checks,
        "failed": [name for name, passed in checks.items() if not passed],
        "banned_tokens": banned,
        "sha256": {
            "N11Formalization.lean": sha256(ROOT_MODULE),
            "EnergyTerminalBatchB13RefineThirteen.lean": sha256(THIRTEEN),
            "EnergyTerminalBatchB13RefineThirteenMain.lean": sha256(MAIN),
            "TARGETS.txt": sha256(TARGETS),
        },
        "ready_for_supervisor_switch": not any(not value for value in checks.values()),
    }
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"ok": report["ready_for_supervisor_switch"],
                      "phase": phase, "failed": report["failed"],
                      "sha256": report["sha256"]}, sort_keys=True))
    raise SystemExit(0 if report["ready_for_supervisor_switch"] else 1)


if __name__ == "__main__":
    main()
