"""Exact synthetic closed-partition guards; no geometry or source replay."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_difference_product_candidate_forest as forest
from n26_sharp_radius_constraints import SCALE
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    matrix = [[0 if i == j else SCALE for j in range(16)] for i in range(16)]
    row = {"index": 29, "sharp_lower": ["0"]*15, "sharp_upper": ["1"]*15}
    nodes = [
        {"kind": "SPLIT", "axis": 0, "mid": "1/2", "children": [1, 2]},
        {"kind": "OPEN"}, {"kind": "OPEN"}]
    left = forest.partition(matrix, row, nodes, forest.tighten, False)
    right = forest.partition(matrix, row, nodes, forest.independently_contract, True)
    if (left != right or len(left) != 2
            or F(left[0]["upper"][0]) != F(1, 2)
            or F(left[1]["lower"][0]) != F(1, 2)):
        raise AssertionError("product closed partition lost its shared half boundary")
    rejected = []

    def reject(name, mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        try:
            forest.partition(matrix, row, bad, forest.independently_contract, True)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("invalid product forest partition accepted: " + name)

    reject("one-closed-half-omitted", lambda bad: bad[0].update(children=[1]))
    reject("two-closed-halves-identified", lambda bad: bad[0].update(children=[1, 1]))
    reject("boolean-child-index", lambda bad: bad[0].update(children=[True, 2]))
    reject("unreachable-hidden-node", lambda bad: bad.append({"kind": "OPEN"}))
    reject("split-boundary-outside-parent", lambda bad: bad[0].update(mid="2"))
    reject("split-boundary-at-parent-endpoint", lambda bad: bad[0].update(mid="0"))
    reject("backward-cycle", lambda bad: bad[0].update(children=[0, 2]))
    reject("nonempty-half-called-EMPTY", lambda bad: bad.__setitem__(1, {"kind": "EMPTY"}))
    reject("unsupported-geometry-mode", lambda bad: bad.__setitem__(1, {"kind": "UNPROVED"}))
    reject("split-has-unknown-proof-fields", lambda bad: bad[0].update(fake_payment=True))
    report = {
        "schema": "N26-difference-product-synthetic-closed-partition-controls-v1",
        "independent_BFS_DFS_two_closed_halves_and_shared_boundary_agreed": True,
        "synthetic_invalid_partition_controls_rejected": rejected,
        "synthetic_NOT_an_actual_root29_partition_or_geometry_acceptance": True,
        "verified": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0, "global_optimality_proved": False,
        "tested_product_forest_module_sha256": binding.sha(forest.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
