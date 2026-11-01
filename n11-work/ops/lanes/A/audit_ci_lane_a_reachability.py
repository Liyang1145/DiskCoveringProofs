#!/usr/bin/env python3
"""Audit whether the n11 workflow can reach lane-A targets.

Scope: workflow/source ordering only.  This is not a Lean kernel check.
"""
from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
WORKFLOW = ROOT / ".github/workflows/n11-lean-build.yml"
LANES = ROOT / "n11-work/ops/lanes"


def main() -> int:
    text = WORKFLOW.read_text(encoding="utf-8")
    match = re.search(r"targets=\$\(cat ([^\n|]+)", text)
    if match is None:
        raise SystemExit("FAIL: target concatenation not found")
    order = re.findall(r"lanes/([A-Z])/TARGETS\.txt", match.group(1))
    present = {lane: (LANES / lane / "TARGETS.txt").is_file() for lane in order}
    a_at = order.index("A") if "A" in order else None
    blockers = order[:a_at] if a_at is not None else []
    print("lane order:", " ".join(order))
    print("lane A position:", a_at + 1 if a_at is not None else "absent")
    print("lanes before A:", " ".join(blockers) if blockers else "none")
    print("present:", present)
    if blockers:
        print("FAIL: lane-A reachability depends on lanes", ",".join(blockers))
        print("required: put A/TARGETS.txt first or build lanes in separate jobs")
        return 1
    print("PASS: no lane targets precede lane A")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
