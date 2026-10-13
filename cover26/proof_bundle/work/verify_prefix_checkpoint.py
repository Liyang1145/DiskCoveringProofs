"""Read-only fresh audit of a saved progress report and current bound files."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import sha
from run_prefix_batch import audit_manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.report.read_text(encoding="utf-8"))
    path = Path(report["latest_checkpoint"])
    if sha(path) != report["checkpoint_sha256"]:
        raise ValueError("checkpoint hash changed")
    manifest = json.loads(path.read_text(encoding="utf-8"))
    result = audit_manifest(manifest)
    expected = {
        "enumeration_completed_subtrees": len(result["completed"]),
        "pending_subtrees_retained": len(result["pending"]),
        "closed_subtree_rooted_graphs": result["closed_rooted"],
        "closed_subtree_distinct_orbits": result["closed_distinct_orbits"],
        "node_limited_tasks_split_not_excluded": result["node_limited_tasks_split_not_excluded"],
        "events_observed": len(manifest["events"]),
        "B18_enumeration_complete": not result["pending"],
    }
    for field, value in expected.items():
        if report[field] != value:
            raise ValueError("progress report overclaims: " + field)
    if report["global_optimality_proved"] or report["arbitrary_cover_reduction_proved"]:
        raise ValueError("unexpected geometric proof claim")
    print(json.dumps({"current_content_recheck_passed": True, **expected}, indent=2), flush=True)


if __name__ == "__main__":
    main()
