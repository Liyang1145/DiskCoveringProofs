"""Structural selector controls only; no mathematical geometry is credited."""

import argparse
import json
from pathlib import Path

import n26_sparse_stage_controls as control


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if any(control.has_split(row) for row in (
        {"kind": "area"}, {"kind": "force"}, {"kind": "split"},
        {"kind": "force_tree", "nodes": [{"kind": "FORCE"}]},
    )):
        raise AssertionError("empty/irrelevant event category became a split-tree fixture")
    if not control.has_split({"kind": "force_tree", "nodes": [{"kind": "SPLIT"}]}):
        raise AssertionError("recorded split-tree category was not recognized")
    report = {
        "schema": "N26-sparse-stage-angular-control-selector-regression-v1",
        "zero_current_force_tree_events_are_a_supported_structural_case": True,
        "zero_split_force_tree_events_are_a_supported_structural_case": True,
        "non_tree_events_never_used_as_angular_controls": True,
        "synthetic_selector_only_not_an_actual_geometry_replay": True,
        "new_geometric_payments": 0,
        "tested_control_helper_sha256": control.exact.sha(control.__file__),
        "executed_test_sha256": control.exact.sha(__file__),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
