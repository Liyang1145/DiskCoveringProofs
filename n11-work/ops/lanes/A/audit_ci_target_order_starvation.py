#!/usr/bin/env python3
"""Lane-A CI build-order starvation audit (offline, STATIC).

The n11-lean-build workflow concatenates, in this order,
  lanes/C/TARGETS.txt lanes/B/TARGETS.txt lanes/A/TARGETS.txt BUILD_TARGETS.txt
and then kernel-builds them serially under a 355-minute job wall clock.  Observed
runs reach only ~10 targets before the job is killed, so any target placed late in
the concatenation is never attempted and can never become "CI green / paid".

This script computes, from the live TARGETS files only, the 1-based position of
lane A's first target and the number of targets that must build before it.  It is
an ordering/budget argument over source files -- NOT a Lean kernel verdict.

Usage: python3 audit_ci_target_order_starvation.py [--out JSON] [--budget N]
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

OPS = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
LANES = ["C", "B", "A"]


def targets(name: str) -> list[str]:
    path = OPS / "lanes" / name / "TARGETS.txt"
    if not path.exists():
        return []
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if s and not s.startswith("#"):
            out.append(s)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(HERE / "ci-target-order-starvation.json"))
    ap.add_argument("--budget", type=int, default=11,
                    help="targets the job is observed to reach before the wall clock")
    args = ap.parse_args()

    counts = {ln: targets(ln) for ln in LANES}
    root = targets("ROOT") if (OPS / "lanes" / "ROOT" / "TARGETS.txt").exists() else []
    if not root and (OPS / "BUILD_TARGETS.txt").exists():
        root = [s.strip() for s in (OPS / "BUILD_TARGETS.txt").read_text().splitlines()
                if s.strip() and not s.strip().startswith("#")]

    seq: list[str] = []
    seen: set[str] = set()
    for ln in LANES:
        for t in counts[ln]:
            if t in seen or t == "N11Formalization":
                continue
            seen.add(t)
            seq.append(t)
    for t in root:
        if t in seen or t == "N11Formalization":
            continue
        seen.add(t)
        seq.append(t)

    lane_a = [t for t in counts["A"]]
    aset = set(lane_a)
    first = next((i for i, t in enumerate(seq) if t in aset), None)
    first_pos = None if first is None else first + 1
    reachable = first is not None and first_pos <= args.budget
    report = {
        "scope": "TARGETS-file ordering + observed CI budget; STATIC, NOT a kernel verdict",
        "counts": {ln: len(counts[ln]) for ln in LANES},
        "total_after_dedup": len(seq),
        "first_lane_a_target": lane_a[0] if lane_a else None,
        "first_lane_a_position_1based": first_pos,
        "targets_preceding_lane_a": first,
        "observed_budget_targets": args.budget,
        "lane_a_reachable_within_budget": reachable,
        "verdict": "LANE_A_STARVED" if not reachable else "LANE_A_REACHABLE",
        "recommendation": (
            "Put lane A first in the build loop (or add a lane-A-only build run); "
            "otherwise no lane-A target can ever be kernel-checked under the 355-min "
            "job wall clock."
        ),
    }
    Path(args.out).write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    print(f"verdict: {report['verdict']}")
    print(f"first lane-A target: {report['first_lane_a_target']} at position "
          f"{first_pos}/{len(seq)} (preceded by {first} targets)")
    print(f"observed CI budget ~{args.budget} targets -> reachable={reachable}")
    print(f"report: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
