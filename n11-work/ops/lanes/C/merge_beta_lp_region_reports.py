#!/usr/bin/env python3
"""Combine exact sign-region checkpoints and audit their overlap/coverage."""
import argparse
import hashlib
import json
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("reports", nargs="+", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--allow-gaps", action="store_true")
    args = parser.parse_args()

    reports = [json.loads(path.read_text()) for path in args.reports]
    ids = {report["id"] for report in reports}
    proposals = {report["proposal_sha256"] for report in reports}
    if len(ids) != 1 or len(proposals) != 1:
        raise SystemExit("reports disagree on id or proposal hash")

    by_mask = {}
    overlaps = 0
    duplicate_conflicts = []
    budget_records = 0
    for path, report in zip(args.reports, reports):
        for item in report["records"]:
            if item["status"] == "time-budget":
                budget_records += 1
                continue
            mask = item["mask"]
            if mask in by_mask:
                overlaps += 1
                if by_mask[mask][1] != item:
                    duplicate_conflicts.append({
                        "mask": mask,
                        "new_report": str(path),
                        "previous": by_mask[mask][1],
                        "current": item,
                    })
            else:
                by_mask[mask] = (path, item)
    if duplicate_conflicts:
        raise SystemExit(json.dumps({
            "error": "conflicting duplicate regions",
            "count": len(duplicate_conflicts),
            "examples": duplicate_conflicts[:3],
        }, indent=1))

    records = [by_mask[mask][1] for mask in sorted(by_mask)]
    masks = sorted(by_mask)
    missing = [mask for mask in range(512) if mask not in by_mask]
    if missing and not args.allow_gaps:
        raise SystemExit(f"coverage has {len(missing)} missing masks; "
                         f"first missing {missing[0]}")

    counts = {}
    gaps = []
    for item in records:
        counts[item["status"]] = counts.get(item["status"], 0) + 1
        if item["status"] == "exact-negative":
            gaps.append(item["exact_gap_float"])
    out = {
        "scope": ("combined exact Fraction active-vertex audit for one public "
                  "residual id; complete-region output is still not a global "
                  "infeasibility proof, kernel credit, or payment"),
        "id": next(iter(ids)),
        "proposal_sha256": next(iter(proposals)),
        "source_reports": [
            {"path": str(path), "sha256": digest(path)}
            for path in args.reports
        ],
        "covered_masks": len(records),
        "missing_masks": missing,
        "overlap_records_checked": overlaps,
        "time_budget_records_skipped": budget_records,
        "status_counts": counts,
        "pass_count": counts.get("PASS", 0),
        "exact_negative_gap_float_min": min(gaps) if gaps else None,
        "exact_negative_gap_float_max": max(gaps) if gaps else None,
        "records": records,
    }
    args.out.write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps({key: out[key] for key in (
        "id", "covered_masks", "missing_masks", "overlap_records_checked",
        "status_counts", "pass_count", "exact_negative_gap_float_min",
        "exact_negative_gap_float_max")}, indent=1))


if __name__ == "__main__":
    main()
