"""Replay an actual angular regression fixture, without paying any new subtree."""

import argparse
import json
from pathlib import Path

import n26_sparse_stage_controls as control


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    fixture, paths = control.select_control(args.stage)
    positive, rejected = control.check_control(
        fixture, control.exact.force.load_trig(args.stage)[0])
    distinct = {control.exact.combinatorics.linux(path): path for path in paths}
    report = {
        "schema": "N26-actual-sparse-stage-angular-regression-control-discovery-v1",
        "verified_stage_geometry": False, "fixture": fixture,
        "actual_positive_angular_tree_replayed": positive,
        "angular_rejection_controls_rejected": rejected,
        "zero_current_tree_events_do_not_skip_angular_rejection_controls": True,
        "new_geometric_payments": 0,
        "files": {text: control.exact.sha(path) for text, path in distinct.items()},
        "executed_probe_sha256": control.exact.sha(__file__),
        "tested_control_helper_sha256": control.exact.sha(control.__file__),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "fixture")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
