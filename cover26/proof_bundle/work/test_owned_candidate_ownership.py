"""Actual-snapshot ownership guards, with no geometric source replay."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
from unittest.mock import patch

import n26_current_owned_candidate_source as source
import verify_owned_candidate_forests as checker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    pending = source.read(args.source / "PENDING-ANGLES.json")
    history, _ = source.history(args.source, pending)
    fresh_row = next(row for row in pending if row["index"] not in history)
    seeded_row = next(row for row in pending if row["index"] in history)
    seed = history[seeded_row["index"]]
    fresh = {
        "source_OPEN_index": fresh_row["index"], "actual_source_closed_box": fresh_row,
        "history_mode": "FRESH", "accepted_history_source": None, "nodes": [{"kind": "OPEN"}],
    }
    seeded = {
        "source_OPEN_index": seeded_row["index"], "actual_source_closed_box": seeded_row,
        "history_mode": "SEEDED", "accepted_history_source": seed["history_source"],
        "nodes": deepcopy(seed["nodes"]),
    }
    initial = {key: val for key, val in seed["accepted_source_classification"].items()
               if key not in ("source_OPEN_index", "actual_source_closed_box")}
    original_values = [None, None, None, None, None, None, None]
    values = ({}, {}, {}, original_values, pending, {"forests": [fresh, seeded]}, history, [])
    rejected = []

    def call(roots):
        with patch.object(checker.base.forest, "replay", return_value=(initial, [], [])):
            return checker.ownership(values, roots)

    control = call([fresh, seeded])
    if control[0]["history_mode"] != "FRESH" or control[1]["history_mode"] != "SEEDED":
        raise AssertionError("actual current ownership modes were not preserved")

    def reject(label, changed):
        try:
            call(changed)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual-snapshot ownership guard passed: " + label)

    reject("duplicate-current-owned-root", [fresh, fresh])
    bad = deepcopy(fresh)
    bad["source_OPEN_index"] = 1958
    reject("previously-discharged-root-reopened", [bad])
    bad = deepcopy(fresh)
    bad["source_OPEN_index"] = True
    reject("boolean-current-root-owner", [bad])
    bad = deepcopy(fresh)
    bad["actual_source_closed_box"]["sharp_lower"][0] = str(F(fresh_row["sharp_lower"][0]) - 1)
    reject("actual-full-root-bounds-changed", [bad])
    bad = deepcopy(fresh)
    bad["history_mode"] = "SEEDED"
    reject("unattempted-root-given-invented-seed", [bad])
    bad = deepcopy(seeded)
    bad["history_mode"], bad["accepted_history_source"] = "FRESH", None
    reject("newest-accepted-seed-reset-as-fresh", [bad])
    bad = deepcopy(seeded)
    bad["accepted_history_source"] = "different-historical-source"
    reject("accepted-seed-source-substituted", [bad])
    bad = deepcopy(seeded)
    next(node for node in bad["nodes"] if node["kind"] == "ENERGY")["certificate"]["eta"] = "-1"
    reject("previous-accepted-energy-leaf-overwritten", [bad])
    report = {
        "schema": "N26-actual-snapshot-fresh-seeded-root-ownership-regression-v1",
        "actual_source_acceptance_sha256": source.sha(args.source / "VERIFIED.json"),
        "actual_pending_roots_sha256": source.sha(args.source / "PENDING-ANGLES.json"),
        "fresh_current_root_index": fresh_row["index"],
        "seeded_current_root_index": seeded_row["index"],
        "actual_snapshot_FRESH_and_SEEDED_mode_control_passed": True,
        "invalid_actual_snapshot_ownership_controls_rejected": rejected,
        "source_snapshot_only_with_mocked_geometry_not_a_geometric_replay": True,
        "new_geometric_candidate_payments": 0,
        "tested_source_sha256": source.sha(source.__file__),
        "tested_ownership_checker_sha256": source.sha(checker.__file__),
        "executed_test_sha256": source.sha(__file__),
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
