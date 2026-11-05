#!/usr/bin/env python3
"""Lane-A C450 CI kernel verdict from the real n11-lean-build job log.

Why this exists: `ops/ci/LATEST.md` embeds only the first 6000 chars of
`summary.json` (the workflow prints `json.dumps(s)[:6000]`), and the build loop
concatenates C,B,A,BUILD_TARGETS before the root.  Lane A's exits therefore fall
off the end of that truncated dump, so LATEST.md cannot show whether
C450ChainCompletion / C450ChainCompletionMain are kernel-green.  This script
fetches the FULL job log for one run (read-only GitHub API) and reports the
exact `=== EXIT` lines for the lane-A C450 targets plus the aggregate exit
counts.  It is an observation of CI output, NOT itself a kernel verdict.

Usage: python3 audit_c450_ci_kernel_verdict.py --run 41847982412 [--job 126636432190]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

REPO = "Liyang1145/DiskCoveringProofs"
HERE = Path(__file__).resolve().parent
TARGETS = ["N11Formalization.C450ChainCompletion",
           "N11Formalization.C450ChainCompletionMain",
           "N11Formalization.C450ChainCompletionAudit"]
EXIT = re.compile(r"=== EXIT (\S+) (\d+)")
AXIOM = re.compile(r"'([^']*C450[^']*)' depends on axioms: \[([^\]]*)\]")
CLEAN = {"propext", "Classical.choice", "Quot.sound"}


def curl(url: str) -> bytes:
    return subprocess.run(["curl", "-sSfL", url], capture_output=True, check=True).stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", required=True)
    ap.add_argument("--job", default=None)
    ap.add_argument("--offline", default=None, help="read an already-downloaded job log")
    ap.add_argument("--out", default=str(HERE / "c450-ci-kernel-verdict.json"))
    args = ap.parse_args()

    job = args.job
    if job is None:
        jobs = json.loads(curl(f"https://api.github.com/repos/{REPO}/actions/runs/{args.run}/jobs"))
        job = str(jobs["jobs"][0]["id"])
    if args.offline:
        log = Path(args.offline).read_text(encoding="utf-8", errors="replace")
    else:
        log = curl(f"https://api.github.com/repos/{REPO}/actions/jobs/{job}/logs").decode("utf-8", "replace")

    exits = EXIT.findall(log)
    lane_a = {t: rc for t, rc in exits if t in TARGETS}
    all_c450 = {t: rc for t, rc in exits if t.startswith("N11Formalization.C450")}
    # the raw log interleaves `MEM ...` lines inside long axiom reports; strip them
    stamp = re.compile(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\.\d+Z")
    def clean(tok: str) -> str:
        return stamp.sub("", tok).strip()
    axioms = {n: sorted({clean(t) for t in a.split(",") if clean(t)}) for n, a in AXIOM.findall(log)}
    dirty = {n: a for n, a in axioms.items() if set(a) - CLEAN}

    report = {
        "scope": "GitHub Actions job log (read-only); observation of CI output, NOT a kernel verdict by this script",
        "repo": REPO, "run_id": args.run, "job_id": job,
        "exit_lines_total": len(exits),
        "exit_zero": sum(1 for _, rc in exits if rc == "0"),
        "exit_nonzero": sum(1 for _, rc in exits if rc != "0"),
        "lane_a_targets": TARGETS,
        "lane_a_exits": lane_a,
        "lane_a_all_green": all(rc == "0" for rc in lane_a.values()) and len(lane_a) == len(TARGETS),
        "c450_exits": all_c450,
        "c450_axiom_decls_seen": len(axioms),
        "c450_axiom_dirty": dirty,
    }
    Path(args.out).write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("run_id", "job_id", "exit_zero",
          "exit_nonzero", "lane_a_exits", "lane_a_all_green",
          "c450_axiom_decls_seen", "c450_axiom_dirty")}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
