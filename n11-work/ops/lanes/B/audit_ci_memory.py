#!/usr/bin/env python3
"""Attribute an n11-lean-build failure from its GitHub job log.

This is a CI-log audit only: it neither builds Lean nor proves a theorem.
"""
from __future__ import annotations

import argparse
import json
import re
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORT = HERE / "audit_ci_memory-report.json"
API = "https://api.github.com/repos/Liyang1145/DiskCoveringProofs"


def get(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": "n11-ci-audit"})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("run_id", nargs="?", default="41289029262")
    parser.add_argument("--log", type=Path, help="use an existing Actions job log")
    args = parser.parse_args()

    jobs = json.loads(get(f"{API}/actions/runs/{args.run_id}/jobs"))["jobs"]
    if len(jobs) != 1:
        raise SystemExit(f"expected one job, found {len(jobs)}")
    job = jobs[0]
    raw = args.log.read_bytes() if args.log else get(job["url"] + "/logs")
    log = raw.decode("utf-8", errors="replace")
    log = re.sub(r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\.\d+Z ?", "", log, flags=re.M)

    builds = [(m.start(), m.group(1)) for m in re.finditer(r"^=== BUILD (\S+)$", log, re.M)]
    exits = {m.group(1): int(m.group(2)) for m in re.finditer(r"^=== EXIT (\S+) (\d+)$", log, re.M)}
    active = [name for _, name in builds if name not in exits]
    # `avail` is already MiB. `ps -eo rss` reports KiB despite the MEM line's
    # abbreviated display, so convert it explicitly.
    mem = [
        (int(a), int(t))
        for a, t in re.findall(r"^MEM \S+ avail=(\d+)MB top: (\d+)", log, re.M)
    ]
    process_errors = [
        line for line in log.splitlines()
        if "error:" in line and not line.lstrip().startswith("##[error]")
    ]
    failed_builds = [
        name for name, code in re.findall(r"^✖ \[\d+/\d+\] Building (\S+) \((\d+)s\)$", log, re.M)
        if int(code) >= 0
    ]
    # `lake` wraps killed processes as `error: Lean exited with code 137`, and
    # its final `error: build failed` is a consequence of those exits. Neither
    # is a Lean diagnostic about a theorem. Keep them separate from real
    # elaboration/kernel errors so an OOM guard cannot be misreported as a
    # mathematical rejection.
    errors = [
        line for line in process_errors
        if "error: Lean exited with code " not in line
        and line.strip() != "error: build failed"
    ]
    runner_shutdown = "The runner has received a shutdown signal" in log
    oom_guard = "OOM-GUARD" in log
    result = {
        "scope": "CI job-log audit only; not a Lean kernel check",
        "run_id": args.run_id,
        "head_sha": job["head_sha"],
        "conclusion": job["conclusion"],
        "active_targets_at_end": active,
        "exits": exits,
        "failed_builds": failed_builds,
        "memory_samples": len(mem),
        "peak_top_rss_kib": max((t for _, t in mem), default=None),
        "peak_top_rss_mib": max((t for _, t in mem), default=None) // 1024
        if mem else None,
        "minimum_available_mb": min((a for a, _ in mem), default=None),
        "oom_guard_triggered": oom_guard,
        "runner_shutdown": runner_shutdown,
        "lean_errors": errors[-20:],
        "process_errors": process_errors[-20:],
        "attribution": (
            "OOM guard killed Lean with no Lean diagnostic"
            if oom_guard and not errors
            else "runner shutdown with no Lean diagnostic"
            if runner_shutdown and not errors
            else "Lean diagnostic present" if errors
            else "inconclusive"
        ),
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
