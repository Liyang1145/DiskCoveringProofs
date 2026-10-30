#!/usr/bin/env python3
"""Static audit of the thirteen-certificate B13 refinement chain.

This checks source/API/count consistency only.  It does not elaborate Lean,
kernel-check a theorem, or pay any residual terminal.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work" / "lean"
FORMALIZATION = LEAN / "N11Formalization"
THIRTEEN = FORMALIZATION / "EnergyTerminalBatchB13RefineThirteen.lean"
MAIN = FORMALIZATION / "EnergyTerminalBatchB13RefineThirteenMain.lean"
TARGETS = LANE / "TARGETS.txt"
CENSUS = ROOT / "n11-work" / "ops" / "lanes" / "C" / "residual389-census.json"
REPORT = LANE / "audit_b13_refine_thirteen-report.json"
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0", "maxRecDepth")
SINGLETONS = (37, 2337, 2341, 2965, 3040, 3112, 3440, 3589, 3623, 3633,
              3777, 3792, 3853)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> None:
    text = THIRTEEN.read_text(encoding="utf-8")
    main_text = MAIN.read_text(encoding="utf-8")
    targets = [line.strip() for line in TARGETS.read_text(encoding="utf-8").splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    residual_ids = set(json.loads(CENSUS.read_text(encoding="utf-8"))["residual_ids"])

    required_imports = (
        "N11Formalization.EnergyTerminalBatchB13RefineTwelve",
        "N11Formalization.EnergyTerminalBatchB13Refine3112",
    )
    required_names = (
        "def newIDs",
        "def paidIDs",
        "theorem new_terminal",
        "theorem new_disjoint_old",
        "theorem new_count : newIDs.card = 13",
        "theorem paid_count : paidIDs.card = 2010",
        "theorem paid_terminal",
        "theorem paid_radius",
        "def RemainingTerminalRadius",
        "theorem remaining_of",
    )
    main_names = (
        "main_of_energy_refineThirteen_and_seven_classes",
        "full_disk_bound_of_energy_refineThirteen_and_seven_classes",
        "EnergyTerminalBatchB13RefineThirteen.remaining_of henergy",
    )
    banned = {token: bool(re.search(r"(?<![\w.])" + re.escape(token) + r"(?![\w])", text))
              for token in BANNED}
    banned_main = {token: bool(re.search(r"(?<![\w.])" + re.escape(token) + r"(?![\w])",
                                         main_text)) for token in BANNED}
    new_target = "N11Formalization.EnergyTerminalBatchB13RefineThirteen"
    main_target = "N11Formalization.EnergyTerminalBatchB13RefineThirteenMain"
    checks = {
        "base_plus_twelve_plus_one_2010": 1997 + 12 + 1 == 2010,
        "residual_minus_thirteen_376": 389 - 13 == 376,
        "thirteen_distinct_singletons": len(SINGLETONS) == len(set(SINGLETONS)) == 13,
        "all_thirteen_are_residual_ids": set(SINGLETONS) <= residual_ids,
        "direct_imports_present": all(f"import {name}" in text for name in required_imports),
        "thirteen_api_complete": all(name in text for name in required_names),
        "main_api_complete": all(name in main_text for name in main_names),
        "thirteen_no_banned_tokens": not any(banned.values()),
        "main_no_banned_tokens": not any(banned_main.values()),
        "thirteen_in_targets_once": targets.count(new_target) == 1,
        "thirteen_main_in_targets_once": targets.count(main_target) == 1,
        "main_follows_thirteen_in_targets": main_target in targets and new_target in targets
            and targets.index(new_target) < targets.index(main_target),
    }
    failed = [name for name, passed in checks.items() if not passed]
    report = {
        "scope": "static source/API/inventory audit only; no Lean elaboration or proof credit",
        "counts": {"base_paid": 1997, "refined_paid": 2010, "refined_residual": 376,
                   "certificates": 13},
        "certificate_ids": list(SINGLETONS),
        "checks": checks,
        "failed": failed,
        "banned_tokens": banned,
        "banned_tokens_main": banned_main,
        "sha256": {
            "EnergyTerminalBatchB13RefineThirteen.lean": sha256(THIRTEEN),
            "EnergyTerminalBatchB13RefineThirteenMain.lean": sha256(MAIN),
            "TARGETS.txt": sha256(TARGETS),
            "residual389-census.json": sha256(CENSUS),
        },
        "ok": not failed,
    }
    REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"ok": report["ok"], "failed": failed, "sha256": report["sha256"]},
                     sort_keys=True))
    raise SystemExit(0 if report["ok"] else 1)


if __name__ == "__main__":
    main()
