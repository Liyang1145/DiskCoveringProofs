"""Synthetic closed-partition regression, not candidate geometry acceptance."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_candidate_energy_local_forest as forest
from n26_sharp_radius_constraints import SCALE
from verify_conditional_force_stage import sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    matrix = [[0 if i == j else SCALE for j in range(16)] for i in range(16)]
    original = {"matrix": matrix, "radius": F(1, 4)}
    row = {"index": 0, "sharp_lower": ["0"] * 15, "sharp_upper": ["1/10"] * 15}
    nodes = [{"kind": "SPLIT", "axis": 0, "mid": "1/20", "children": [1, 2]},
             {"kind": "OPEN"}, {"kind": "OPEN"}]
    result, pending, ledger = forest.replay(original, None, None, row, nodes)
    if (result["source_candidate_root_fully_lower_bounded"] or len(pending) != 2 or ledger
            or pending[0]["upper"][0] != "1/20" or pending[1]["lower"][0] != "1/20"):
        raise AssertionError("synthetic candidate closed partition lost its shared boundary")
    rejected = []

    def reject(label, changed):
        try:
            forest.replay(original, None, None, row, changed)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid closed candidate forest accepted: " + label)

    bad = deepcopy(nodes)
    bad[0]["children"][1] = 1
    reject("lost-shared-closed-half", bad)
    reject("hidden-unvisited-OPEN-node", nodes + [{"kind": "OPEN"}])
    reject("nonempty-root-marked-empty", [{"kind": "EMPTY"}])
    bad = deepcopy(nodes)
    bad[0]["mid"] = "1/10"
    reject("split-at-outer-endpoint", bad)
    bad = deepcopy(nodes)
    bad[0]["children"][0] = 0
    reject("cyclic-candidate-child", bad)
    bad = deepcopy(nodes)
    bad[1]["unverified_proof"] = True
    reject("OPEN-carries-hidden-proof-field", bad)
    bad = deepcopy(nodes)
    bad[1]["kind"] = "QUADRATIC_ENERGY"
    reject("full-type-energy-leaf-relabelled-as-candidate", bad)
    bad = deepcopy(nodes)
    bad[0]["independent_closed_half_ignored"] = True
    reject("split-has-unknown-field", bad)
    bad = deepcopy(nodes)
    bad[1] = {"kind": "LOCAL", "supplied_hull": []}
    reject("LOCAL-hull-supplied-instead-of-reconstructed", bad)
    report = {"schema": "N26-candidate-energy-LOCAL-closed-partition-regression-evidence-v1",
              "synthetic_structure_regression_only": True,
              "independent_BFS_DFS_shared_closed_boundary_control": result,
              "invalid_partition_controls_rejected": rejected,
              "actual_candidate_LOCAL_or_energy_certificates_not_proved_by_this_test": True,
              "current_candidate_source_roots_removed": 0,
              "global_lower_bound_proved": False, "global_optimality_proved": False,
              "tested_forest_sha256": sha(forest.__file__), "executed_test_sha256": sha(__file__)}
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
