"""Read-only fresh audit of all four new-scope queue checkpoints."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import WORK, publish
from run_new_scope_batch import audit, report_values, sha


def verify_current():
    outputs = WORK.parent / "outputs"
    rows, files = [], [Path(__file__), WORK / "run_new_scope_batch.py"]
    for b in (14, 15, 16, 17):
        report_path = outputs / f"n26-new-B{b}-progress-v1.json"
        report = json.loads(report_path.read_text())
        if not (report["verified_partition_bookkeeping"] and report["B"] == b
                and not report["global_optimality_proved"]
                and not report["arbitrary_cover_reduction_accepted"]
                and len(report["negative_controls_rejected"]) >= 5):
            raise ValueError("wrong family progress claim")
        checkpoint_path = Path(report["latest_checkpoint"])
        if sha(checkpoint_path) != report["checkpoint_sha256"]:
            raise ValueError("checkpoint byte hash changed")
        manifest = json.loads(checkpoint_path.read_text())
        if manifest["B"] != b:
            raise ValueError("checkpoint from another family")
        result = audit(manifest)
        values = report_values(result)
        if any(report[k] != v for k, v in values.items()):
            raise ValueError("progress report differs from fresh audit")
        rows.append({"B": b, "I": 26 - b, **values,
                     "checkpoint_sha256": sha(checkpoint_path)})
        files.extend((report_path, checkpoint_path))
    return rows, files


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    rows, files = verify_current()
    report = {
        "schema": "N26-four-new-scope-checkpoints-fresh-content-audit-v1",
        "all_four_current_checkpoints_replayed": True, "families": rows,
        "completed_subtrees": sum(r["completed_subtrees"] for r in rows),
        "pending_subtrees": sum(r["pending_subtrees"] for r in rows),
        "catalog_graphs_still_require_geometric_lower_certificates": True,
        "N26_complete_catalog": False, "global_optimality_proved": False,
        "arbitrary_cover_reduction_accepted": False,
        "files": {str(path): sha(path) for path in files},
    }
    publish(args.output, report)
    print(json.dumps({k: v for k, v in report.items() if k != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
