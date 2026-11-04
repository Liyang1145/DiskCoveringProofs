#!/usr/bin/env python3
"""Quantify lane-B starvation in the n11 CI build order.

The workflow concatenates lane C (239 targets) before lane B (34) and lane A
(77), then runs one serial `lake build` per target under a ~355 min job cap.
This script reads a completed run's summary.json exits (as mirrored into
`ops/ci/LATEST.md`) plus the lane TARGETS lists, and reports how many targets of
each lane were actually reached.  A lane whose targets never appear is starved,
not red.  Static CI-log audit only -- not a Lean kernel check, pays no radius.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LANES = ("C", "B", "A")


def targets_for(lane: str) -> list[str]:
    path = ROOT / "n11-work" / "ops" / "lanes" / lane / "TARGETS.txt"
    return [ln.strip() for ln in path.read_text(encoding="utf-8").splitlines()
            if ln.strip() and not ln.lstrip().startswith("#")]


def parse_exits(latest: Path) -> list[tuple[str, str]]:
    text = latest.read_text(encoding="utf-8")
    i = text.find("## summary.json")
    blk = text[i:text.find("```", text.find("```", i) + 3)]
    return re.findall(r'"(N11Formalization[."A-Za-z0-9_]*)"\s*,\s*"(\d)"', blk)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--latest", type=Path, default=ROOT / "n11-work/ops/ci/LATEST.md")
    ap.add_argument("--out", type=Path,
                    default=HERE / "audit_ci_lane_b_starvation-report.json")
    args = ap.parse_args()

    exits = parse_exits(args.latest)
    lanes = {lane: set(targets_for(lane)) for lane in LANES}
    reached = {lane: [m for m, _ in exits if m in lanes[lane]] for lane in LANES}
    reds = [m for m, e in exits if e != "0"]
    report = {
        "scope": "CI build-order audit from ops/ci/LATEST.md; not a kernel check",
        "exits_entries": len(exits),
        "lane_target_counts": {lane: len(lanes[lane]) for lane in LANES},
        "lane_reached_counts": {lane: len(reached[lane]) for lane in LANES},
        "lane_b_reached": reached["B"],
        "reds": reds,
        "reds_by_lane": {lane: [m for m in reds if m in lanes[lane]] for lane in LANES},
    }
    report["lane_b_starved"] = len(reached["B"]) == 0
    args.out.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
