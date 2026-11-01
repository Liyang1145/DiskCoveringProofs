#!/usr/bin/env python3
"""Diagnose whether lane-C targets prevent CI from reaching lane B's census."""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OPS = ROOT / "n11-work/ops"
WORKFLOW = ROOT / ".github/workflows/n11-lean-build.yml"
REPORT = HERE / "audit_ci_target_order-report.json"
STRUCTURAL = (
    "N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus"
)
CONFLICTED = "N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus"
LANES = ("C", "B", "A")


def targets(path):
    return [
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


ordered = []
for lane in LANES:
    ordered.extend(targets(OPS / "lanes" / lane / "TARGETS.txt"))
ordered.extend(targets(OPS / "BUILD_TARGETS.txt"))

seen = set()
ordered = [name for name in ordered if not (name in seen or seen.add(name))]
workflow = WORKFLOW.read_text(encoding="utf-8")
workflow_order = re.search(r"targets=\$\(cat ([^\n|]+)", workflow)
declared_lane_order = re.findall(r"lanes/([A-Z])/TARGETS\.txt", workflow_order.group(1)) \
    if workflow_order else []

structural_pos = ordered.index(STRUCTURAL) if STRUCTURAL in ordered else None
conflicted_pos = ordered.index(CONFLICTED) if CONFLICTED in ordered else None
blocked = (
    structural_pos is not None
    and conflicted_pos is not None
    and conflicted_pos < structural_pos
)
result = {
    "scope": "static CI target-order audit only; not a Lean kernel check",
    "ok": declared_lane_order == list(LANES) and structural_pos is not None,
    "workflow_lane_order": declared_lane_order,
    "structural_target": STRUCTURAL,
    "structural_position": structural_pos,
    "conflicted_target": CONFLICTED,
    "conflicted_position": conflicted_pos,
    "blocked_before_structural": blocked,
    "conclusion": (
        "CI reaches lane C's conflicted literal census before lane B's structural "
        "census; reordering inside B/TARGETS.txt cannot avoid it"
        if blocked else "lane B structural census is not preceded by the conflicted target"
    ),
    "sha256": {
        str(path.relative_to(ROOT)): sha256(path)
        for path in (
            WORKFLOW,
            OPS / "lanes/C/TARGETS.txt",
            OPS / "lanes/B/TARGETS.txt",
        )
    },
}
REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(result, sort_keys=True))
raise SystemExit(0 if result["ok"] else 1)
