"""Synthetic per-root history-picker controls; no geometric payments."""

import argparse
from copy import deepcopy
import json
from pathlib import Path
from unittest.mock import patch

from audit_prefix_partition import linux
import n26_current_owned_candidate_source as source


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    root = Path(__file__).resolve().parent
    newest, earlier, stop = (root / ("owned-history-fixture-" + name) for name in ("new", "old", "stop"))
    row_a = {"index": 1794, "sharp_lower": ["0"], "sharp_upper": ["1"]}
    row_b = {"index": 957, "sharp_lower": ["0"], "sharp_upper": ["1"]}
    rows = [row_a, row_b]
    new_nodes = [{"kind": "SPLIT", "axis": 0, "mid": "1/2", "children": [1, 2]},
                 {"kind": "OPEN"}, {"kind": "OPEN"}]
    old_nodes = [{"kind": "OPEN"}]
    fixture = {}

    def insert(folder, prior, forest_rows):
        fixture[linux(folder / "VERIFIED.json")] = {"schema": source.SCHEMA, "verified": True}
        fixture[linux(folder / "MANIFEST.json")] = {"source": linux(prior)}
        fixture[linux(folder / "PROPOSAL.json")] = {
            "forests": [{"source_OPEN_index": row["index"], "actual_source_closed_box": row, "nodes": nodes}
                        for row, nodes in forest_rows]
        }
        fixture[linux(folder / "ROOT-CLASSIFICATION.json")] = [
            {"source_OPEN_index": row["index"], "actual_source_closed_box": row,
             "source_candidate_root_fully_lower_bounded": False} for row, _ in forest_rows
        ]

    insert(newest, earlier, [(row_a, new_nodes)])
    insert(earlier, stop, [(row_a, old_nodes), (row_b, old_nodes)])
    fixture[linux(stop / "VERIFIED.json")] = {"schema": "synthetic-history-stop"}
    rejected = []

    def run(data, incoming=rows):
        with patch.object(source, "read", side_effect=lambda path: data[linux(path)]), \
             patch.object(source.binding, "bound", return_value=({"verified": True}, [])), \
             patch.object(source, "sha", return_value="synthetic-not-a-geometric-digest"):
            return source.history(newest, incoming)[0]

    actual = run(fixture)
    if (
        actual[1794]["nodes"] != new_nodes
        or actual[1794]["history_source"] != linux(newest)
        or actual[957]["nodes"] != old_nodes
        or actual[957]["history_source"] != linux(earlier)
        or run(fixture, [{"index": 959}])
    ):
        raise AssertionError("history picker did not retain newest and other-root older forests")

    def reject(label, data, incoming=rows):
        try:
            run(data, incoming)
        except (ValueError, KeyError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError("invalid synthetic root history accepted: " + label)

    reject("duplicate-current-root-index", fixture, rows + rows[:1])
    bad = deepcopy(fixture)
    bad[linux(newest / "MANIFEST.json")]["source"] = linux(newest)
    reject("cyclic-source-history", bad)
    bad = deepcopy(fixture)
    bad[linux(newest / "PROPOSAL.json")]["forests"][0]["actual_source_closed_box"]["sharp_upper"][0] = "2"
    reject("historical-full-source-box-changed", bad)
    bad = deepcopy(fixture)
    bad[linux(newest / "ROOT-CLASSIFICATION.json")][0]["source_candidate_root_fully_lower_bounded"] = True
    reject("discharged-root-reopened-as-current", bad)
    bad = deepcopy(fixture)
    bad[linux(newest / "ROOT-CLASSIFICATION.json")].append(deepcopy(
        bad[linux(newest / "ROOT-CLASSIFICATION.json")][0]
    ))
    reject("duplicate-historical-classification", bad)
    bad = deepcopy(fixture)
    bad[linux(newest / "PROPOSAL.json")]["forests"].append(deepcopy(
        bad[linux(newest / "PROPOSAL.json")]["forests"][0]
    ))
    reject("duplicate-historical-forest-owner", bad)
    bad = deepcopy(fixture)
    bad[linux(newest / "PROPOSAL.json")]["forests"][0]["source_OPEN_index"] = True
    reject("boolean-original-owner", bad)
    bad = deepcopy(fixture)
    bad[linux(newest / "ROOT-CLASSIFICATION.json")][0]["actual_source_closed_box"] = row_b
    reject("classification-full-root-owner-substituted", bad)
    report = {
        "schema": "N26-per-root-accepted-forest-history-picker-regression-v1",
        "newest_root_forest_and_other_older_root_forest_preserved": True,
        "unattempted_current_root_has_no_invented_seed": True,
        "invalid_history_controls_rejected": rejected,
        "synthetic_history_only_not_an_actual_geometric_source_replay": True,
        "new_geometric_candidate_payments": 0,
        "tested_source_sha256": source.binding.sha(source.__file__),
        "executed_test_sha256": source.binding.sha(__file__),
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
