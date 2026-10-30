#!/usr/bin/env python3
"""Static block audit for the B13 descent-bound module.

This verifies the source hierarchy and forbidden-token absence.  It is not a
Lean elaboration check and provides no proof credit.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
MODULE = LEAN / "EnergyTerminalBatchB13DescentBounds.lean"
B13 = LEAN / "EnergyTerminalBatchB13.lean"
REPORT = LANE / "audit_b13_descent-report.json"
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0", "maxRecDepth")


def main() -> None:
    text = MODULE.read_text(encoding="utf-8")
    b13 = B13.read_text(encoding="utf-8")
    groups = re.findall(r"private theorem g(\d{2})_lt ", text)
    checks = {
        "ten_group_blocks": groups == [f"{i:02d}" for i in range(3, 13)],
        "kernel_decisions_12": text.count("decide +kernel") == 12,
        "b09_single_decode": "∀ m ∈ EnergyTerminalBatchB09.paidIDs, m.val < 2565" in text,
        "first42_single_decode": "∀ m ∈ Paid16GeneralFirst42.newIDs, m.val < 2565" in text,
        "remaining210_no_direct_decode":
            "∀ m ∈ Paid16GeneralRemaining210.newIDs, m.val < 2565" not in text,
        "b13_imports_module": "import N11Formalization.EnergyTerminalBatchB13DescentBounds" in b13,
        "b13_uses_blocked_b10": "EnergyTerminalBatchB13DescentBounds.b10_lt n hn" in b13,
        "b13_uses_blocked_210": "EnergyTerminalBatchB13DescentBounds.remaining210_lt n hn" in b13,
        "no_forbidden_tokens": not any(
            re.search(r"(?<![\w.])" + re.escape(t) + r"(?![\w])", text + b13)
            for t in BANNED
        ),
    }
    result = {
        "module": str(MODULE.relative_to(ROOT)),
        "group_blocks": len(groups),
        "kernel_decisions": text.count("decide +kernel"),
        "largest_claimed_literal_decode": 58,
        "checks": checks,
        "scope": "static source hierarchy only; Lean elaboration is CI-pending",
        "ok": all(checks.values()),
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
