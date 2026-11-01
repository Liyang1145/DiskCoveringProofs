#!/usr/bin/env python3
"""Extract lane progress and the first failure from an n11 Lean build log.

This is a CI log audit, not a Lean kernel check.  It distinguishes a target
that ran from targets merely listed in TARGETS.txt, which matters when an OOM
in an earlier lane prevents a lane-B target from being checked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def targets_for(lane: str) -> list[str]:
    path = ROOT / "n11-work" / "ops" / "lanes" / lane / "TARGETS.txt"
    return [line.strip() for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("log", type=Path)
    parser.add_argument("--run", required=True)
    parser.add_argument("--sha", required=True)
    parser.add_argument("--out", type=Path,
                        default=HERE / "audit_ci_log_progress-report.json")
    args = parser.parse_args()

    raw = args.log.read_bytes()
    text = raw.decode("utf-8", errors="replace")
    builds = re.findall(r"=== BUILD (N11Formalization(?:\.[A-Za-z0-9_]+)*)", text)
    exits = re.findall(r"=== EXIT (N11Formalization(?:\.[A-Za-z0-9_]+)*) (\d+)", text)
    replayed = re.findall(r"Replayed (N11Formalization(?:\.[A-Za-z0-9_]+)*)", text)
    oom_guard = bool(re.search(r"OOM-GUARD killing lean \(avail=\d+MB\)", text))
    shutdown = "runner has received a shutdown signal" in text
    exit_143 = bool(re.search(r"Process completed with exit code 143", text))

    lane_targets = {lane: set(targets_for(lane)) for lane in ("A", "B", "C")}
    reached_by_lane = {
        lane: [target for target in builds if target in lane_targets[lane]]
        for lane in lane_targets
    }
    first_lane = next((lane for lane in ("A", "B", "C")
                       if any(target in lane_targets[lane] for target in builds[:1])), None)
    b_targets_reached = bool(reached_by_lane["B"])
    exited = {target for target, _ in exits}
    started_without_exit = [target for target in builds if target not in exited]
    result = {
        "scope": "CI execution-log audit only; not a Lean kernel check or proof",
        "run": args.run,
        "head_sha": args.sha,
        "log_sha256": hashlib.sha256(raw).hexdigest().upper(),
        "build_count": len(builds),
        "build_targets": builds,
        "exit_records": [{"target": target, "exit": int(code)} for target, code in exits],
        "started_without_exit": started_without_exit,
        "last_started_without_exit": started_without_exit[-1] if started_without_exit else None,
        "replayed_count": len(replayed),
        "last_replayed": replayed[-1] if replayed else None,
        "first_lane": first_lane,
        "targets_reached_by_lane": reached_by_lane,
        "lane_b_target_reached": b_targets_reached,
        "oom_guard_triggered": oom_guard,
        "runner_shutdown": shutdown,
        "exit_143": exit_143,
        "diagnosis": (
            "Lane-B targets were not reached before the runner stopped."
            if not b_targets_reached else
            "At least one lane-B target was reached; inspect its exit record."
        ),
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
