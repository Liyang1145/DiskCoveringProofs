#!/usr/bin/env python3
"""Static block audit for the B13 descent-bound module.

This verifies the source hierarchy and forbidden-token absence.  It is not a
Lean elaboration check and provides no proof credit.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
MODULE = LEAN / "EnergyTerminalBatchB13DescentBounds.lean"
B13 = LEAN / "EnergyTerminalBatchB13.lean"
REPORT = LANE / "audit_b13_descent-report.json"
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0")


def main() -> None:
    text = MODULE.read_text(encoding="utf-8")
    b13 = B13.read_text(encoding="utf-8")
    before_emit = MODULE.read_bytes()
    subprocess.run(
        [sys.executable, str(LANE / "emit_b13_descent_bounds.py")],
        cwd=ROOT, check=True, capture_output=True,
    )
    emitter_matches = before_emit == MODULE.read_bytes()
    groups = re.findall(r"private theorem g(\d{2})_lt ", text)
    high_match = re.search(
        r"def b09HighIDs : Finset \(Fin 5011\) := \{([0-9,]+)\}", text)
    source_high_ids = set(map(int, high_match.group(1).split(","))) if high_match else set()
    literal_ids: set[int] = set()
    literal_blocks = 0
    for path in sorted(LEAN.glob("Paid16GeneralNext1182S*.lean")):
        for body in re.findall(
                r"^def ids\d+ : Finset \(Fin 5011\) := \{([0-9,]+)\}",
                path.read_text(encoding="utf-8"), re.MULTILINE):
            literal_ids.update(map(int, body.split(",")))
            literal_blocks += 1
    checks = {
        "ten_group_blocks": groups == [f"{i:02d}" for i in range(3, 13)],
        "kernel_decisions_12": text.count("decide +kernel") == 12,
        "b09_high_classification":
            "∀ m ∈ EnergyTerminalBatchB09.paidIDs, m.val < 2565 ∨ m ∈ b09HighIDs" in text and
            "def b09HighIDs : Finset (Fin 5011) :=" in text,
        "high_ids_excluded": "theorem high_not_next" in text,
        "high_ids_27": len(source_high_ids) == 27,
        "next1182_literals_57x1182":
            literal_blocks == 57 and len(literal_ids) == 1182,
        "high_ids_absent_from_next1182": not (source_high_ids & literal_ids),
        "bounded_rec_depth": text.count("set_option maxRecDepth 10000") == 1,
        "emitter_reproduces_module": emitter_matches,
        "first42_single_decode": "∀ m ∈ Paid16GeneralFirst42.newIDs, m.val < 2565" in text,
        "remaining210_no_direct_decode":
            "∀ m ∈ Paid16GeneralRemaining210.newIDs, m.val < 2565" not in text,
        "b13_imports_module": "import N11Formalization.EnergyTerminalBatchB13DescentBounds" in b13,
        "b13_uses_b11_bound": "EnergyTerminalBatchB13DescentBounds.b11_bound n hn" in b13,
        "b13_uses_high_exclusion": "EnergyTerminalBatchB13DescentBounds.high_not_next a" in b13,
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
        "high_ids": len(source_high_ids),
        "next1182_literal_blocks": literal_blocks,
        "next1182_literal_ids": len(literal_ids),
        "checks": checks,
        "scope": "static source hierarchy only; Lean elaboration is CI-pending",
        "ok": all(checks.values()),
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
