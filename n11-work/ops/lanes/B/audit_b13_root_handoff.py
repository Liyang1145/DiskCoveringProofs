#!/usr/bin/env python3
"""Audit the exact B12Main -> B13Main root handoff requested by lane B.

This is a source/import audit, not Lean elaboration or proof credit.  It accepts
either exactly one old import (pre-handoff) or exactly one new import
(post-handoff), and checks that the replacement target has the expected imports
and public declarations.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean"
ROOT_MODULE = LEAN / "N11Formalization.lean"
MAIN = LEAN / "N11Formalization" / "EnergyTerminalBatchB13Main.lean"
TARGETS = Path(__file__).with_name("TARGETS.txt")
REPORT = Path(__file__).with_name("audit_b13_root_handoff-report.json")

OLD = "import N11Formalization.EnergyTerminalBatchB12Main"
NEW = "import N11Formalization.EnergyTerminalBatchB13Main"
REQUIRED_IMPORTS = {
    "import N11Formalization.C450ChainCompletionMain",
    "import N11Formalization.EnergyTerminalBatchB13",
    "import N11Formalization.ActualMetricClassReduction",
}
REQUIRED_NAMES = {
    "main_of_energy_b13_and_seven_classes",
    "full_disk_bound_of_energy_b13_and_seven_classes",
}
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0", "maxRecDepth")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def classify_root(root_text: str) -> tuple[str, bool, bool]:
    """Return (phase, has_one_old_import, has_one_new_import)."""
    old_count = root_text.splitlines().count(OLD)
    new_count = root_text.splitlines().count(NEW)
    if old_count == 1 and new_count == 0:
        return "pre_handoff", True, False
    if old_count == 0 and new_count == 1:
        return "post_handoff", False, True
    return "invalid", old_count == 1, new_count == 1


def audit(root_module: Path = ROOT_MODULE, targets_path: Path = TARGETS,
          main_path: Path = MAIN, report_path: Path | None = REPORT) -> dict:
    root_text = root_module.read_text(encoding="utf-8")
    main_text = main_path.read_text(encoding="utf-8")
    targets = [line.strip() for line in targets_path.read_text(encoding="utf-8").splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    imports = set(re.findall(r"^import\s+(N11Formalization(?:\.\w+)+)\s*$",
                             main_text, re.MULTILINE))
    missing_imports = sorted(
        item.removeprefix("import N11Formalization.")
        for item in REQUIRED_IMPORTS if item not in main_text.splitlines()
    )
    forbidden = [token for token in BANNED
                 if re.search(r"(?<![\w.])" + re.escape(token) + r"(?![\w])", main_text)]
    phase, has_one_old, has_one_new = classify_root(root_text)
    checks = {
        "root_has_exactly_one_valid_import": phase != "invalid",
        "b13main_in_targets_once": targets.count("N11Formalization.EnergyTerminalBatchB13Main") == 1,
        "b13main_follows_b13": (
            "N11Formalization.EnergyTerminalBatchB13" in targets
            and targets.index("N11Formalization.EnergyTerminalBatchB13")
            < targets.index("N11Formalization.EnergyTerminalBatchB13Main")
        ),
        "required_imports_present": not missing_imports,
        "required_names_present": REQUIRED_NAMES <= set(re.findall(r"\b\w+\b", main_text)),
        "no_forbidden_tokens": not forbidden,
    }
    result = {
        "root_module": str(root_module),
        "root_import_phase": phase,
        "observed_old_import_count": root_text.splitlines().count(OLD),
        "observed_new_import_count": root_text.splitlines().count(NEW),
        "requested_old_import": OLD,
        "requested_new_import": NEW,
        "b13main": str(main_path),
        "b13main_sha256": digest(main_path),
        "b13main_imports": sorted(imports),
        "missing_required_imports": missing_imports,
        "forbidden_tokens": forbidden,
        "checks": checks,
        "root_still_pre_handoff": phase == "pre_handoff",
        "root_successfully_post_handoff": phase == "post_handoff",
        "replacement_ready_for_review": all(checks.values()),
        "scope": "static source/import audit only; no Lean elaboration or root CI verdict",
    }
    if report_path is not None:
        report_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                               encoding="utf-8")
    return result


def main() -> None:
    root_module = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT_MODULE
    result = audit(root_module=root_module,
                   report_path=REPORT if root_module == ROOT_MODULE else None)
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if all(result["checks"].values()) else 1)


if __name__ == "__main__":
    main()
