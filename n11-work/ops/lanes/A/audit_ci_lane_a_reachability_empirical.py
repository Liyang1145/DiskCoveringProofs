#!/usr/bin/env python3
"""Empirical lane-A CI reachability audit from the real n11-lean-build job logs.

Scope: reads GitHub Actions job logs for the public repo (read-only GET).  This is
NOT a Lean kernel verdict; it only reports which lane-A targets the CI build loop
actually attempted and where each run stopped.

Usage:
  python3 audit_ci_lane_a_reachability_empirical.py [--runs N] [--offline LOG]...
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = "Liyang1145/DiskCoveringProofs"
WORKFLOW = "n11-lean-build.yml"
HERE = Path(__file__).resolve().parent
OUT = HERE / "ci-lane-a-reachability.json"

LANE_A = re.compile(r"N11Formalization\.(C450ChainCompletion\w*)")
BUILD = re.compile(r"=== BUILD (\S+)")
EXIT = re.compile(r"=== EXIT (\S+) (\d+)")
STOP = re.compile(r"shutdown signal|Process completed with exit code|timeout 90m")


def api(path: str) -> object:
    out = subprocess.run(
        ["curl", "-sSfL", "-H", "Accept: application/vnd.github+json",
         f"https://api.github.com/repos/{REPO}/{path}"],
        capture_output=True, check=True,
    ).stdout
    return json.loads(out)


def fetch_log(job_id: int) -> str:
    out = subprocess.run(
        ["curl", "-sSfL",
         f"https://api.github.com/repos/{REPO}/actions/jobs/{job_id}/logs"],
        capture_output=True, check=True,
    ).stdout
    return out.decode("utf-8", "replace")


def analyse(log: str) -> dict:
    builds = [m.group(1) for m in BUILD.finditer(log)]
    exits = [(m.group(1), int(m.group(2))) for m in EXIT.finditer(log)]
    a_builds = [t for t in builds if LANE_A.search(t)]
    a_exits = [(t, rc) for t, rc in exits if LANE_A.search(t)]
    stop = STOP.search(log)
    return {
        "targets_attempted": len(builds),
        "targets_exited": len(exits),
        "last_target_attempted": builds[-1] if builds else None,
        "lane_a_attempted": a_builds,
        "lane_a_exits": a_exits,
        "stopped_mid_target": bool(stop),
        "non_zero_exits": [t for t, rc in exits if rc != 0],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--offline", nargs="*", default=[])
    args = ap.parse_args()

    records = []
    if args.offline:
        for i, path in enumerate(args.offline):
            log = Path(path).read_text(encoding="utf-8", errors="replace")
            records.append({"source": path, **analyse(log)})
    else:
        runs = api(f"actions/workflows/{WORKFLOW}/runs?per_page={args.runs}")["workflow_runs"]
        for run in runs:
            jobs = api(f"actions/runs/{run['id']}/jobs")["jobs"]
            for job in jobs:
                log = fetch_log(job["id"])
                records.append({
                    "run_id": run["id"], "sha": run["head_sha"][:8],
                    "conclusion": run["conclusion"], "job_id": job["id"],
                    **analyse(log),
                })

    reached = [r for r in records if r["lane_a_attempted"]]
    green = [r for r in records if r["lane_a_exits"] and all(rc == 0 for _, rc in r["lane_a_exits"])]
    report = {
        "scope": "GitHub Actions job logs, read-only; NOT a Lean kernel verdict",
        "runs_analysed": len(records),
        "runs_reaching_lane_a": len(reached),
        "runs_with_green_lane_a_exit": len(green),
        "records": records,
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    for r in records:
        print(f"run {r.get('run_id','-')} sha {r.get('sha','-')} {r.get('conclusion','-'):9} "
              f"attempted={r['targets_attempted']:3} last={r['last_target_attempted']} "
              f"laneA={r['lane_a_attempted']} stopped_mid={r['stopped_mid_target']}")
    print(f"-> {OUT.name}: runs={len(records)} reaching_laneA={len(reached)} green_laneA={len(green)}")
    return 0 if reached else 1


if __name__ == "__main__":
    raise SystemExit(main())
