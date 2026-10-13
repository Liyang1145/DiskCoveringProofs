"""Exact policy guards and actual contained root-tight shared-half partition."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import resume_support_cost_refined_forest as producer
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    accepted = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != accepted
            or binding.sha(args.resource / "CONTEXT.json") != accepted["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != accepted["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("split-policy controls changed fixed arithmetic DATA")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    source = binding.read(args.source / "VERIFIED.json")
    digest = binding.sha(args.source / "PENDING-ANGLES.json")
    if source["files"]["PENDING-ANGLES.json"] != digest:
        raise ValueError("split policy actual root DATA changed")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json") if row["index"] == 28)
    lo, hi = producer.BASE.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    narrow = next(axis for axis, (a, b) in enumerate(zip(lo, hi)) if 0 < b-a <= F(1, 10**7))
    contributions = ["0"]*15
    contributions[narrow] = "-1"
    selected = producer.split_axis(lo, hi, contributions, "support-loss")
    if (selected["axis"] != narrow
            or selected["heuristic_selection_NOT_a_new_lower_bound_or_geometric_certificate"] is not True):
        raise AssertionError("support-cost policy lost an actually narrow eligible coordinate")
    midpoint = (lo[narrow]+hi[narrow])/2
    nodes = [{"kind": "SPLIT", "axis": narrow, "mid": str(midpoint), "children": [1, 2]},
             {"kind": "OPEN"}, {"kind": "OPEN"}]
    dfs = forest.partition(original["matrix"], row, nodes, producer.BASE.tighten, False)
    bfs = forest.partition(original["matrix"], row, nodes, producer.BASE.independently_contract, True)
    if (dfs != bfs or len(dfs) != 2
            or F(dfs[0]["upper"][narrow]) != midpoint
            or F(dfs[1]["lower"][narrow]) != midpoint):
        raise AssertionError("actual root-tight split lost a closed shared boundary or independent contraction")
    if producer.split_axis(lo, hi, ["0"]*15, "support-loss")["axis"] != producer.split_axis(
            lo, hi, None, "widest-all")["axis"]:
        raise AssertionError("zero-loss support policy did not fall back to actual widest eligible coordinate")
    if producer.split_axis(lo, lo, contributions, "support-loss") is not None:
        raise AssertionError("singleton closed domain acquired an invented split")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid support-cost policy accepted: "+label)

    reject("support-cost-unknown-policy", lambda: producer.split_axis(lo, hi, contributions, "unproved"))
    reject("support-cost-wrong-domain-dimension", lambda: producer.split_axis(lo[:14], hi, contributions, "support-loss"))
    reverse = list(lo)
    reverse[narrow] = hi[narrow]+1
    reject("support-cost-reversed-closed-domain", lambda: producer.split_axis(reverse, hi, contributions, "support-loss"))
    reject("support-cost-missing-contribution", lambda: producer.split_axis(lo, hi, contributions[:14], "support-loss"))
    reject("support-cost-noncanonical-type-contribution", lambda: producer.split_axis(lo, hi, [0]*15, "support-loss"))
    for label, mutation in (
        ("actual-root-tight-split-half-omitted", lambda bad: bad[0].update(children=[1])),
        ("actual-root-tight-split-halves-identified", lambda bad: bad[0].update(children=[1, 1])),
        ("actual-root-tight-split-unreachable-hidden-node", lambda bad: bad.append({"kind": "OPEN"})),
    ):
        def call(mutation=mutation):
            bad = deepcopy(nodes)
            mutation(bad)
            forest.partition(original["matrix"], row, bad, producer.BASE.independently_contract, True)
        reject(label, call)
    if binding.sha(args.source / "PENDING-ANGLES.json") != digest:
        raise ValueError("actual source root DATA changed during split-policy controls")
    report = {
        "schema": "N26-support-cost-all-coordinate-split-policy-arithmetic-controls-v1",
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "actual_source_root_DATA_sha256": digest, "actual_root": 28,
        "actual_root_tight_nonzero_coordinate_split_checked": narrow,
        "both_closed_halves_and_exact_shared_boundary_independently_reconstructed": True,
        "actual_split_leaf_domains": dfs,
        "support_cost_selection_heuristic_is_NOT_a_lower_bound_or_payment": True,
        "invalid_policy_and_actual_shared_half_controls_rejected": rejected,
        "complete_latest_source_model_history_geometry_gate_NOT_performed": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_producer_sha256": binding.sha(producer.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_root_tight_split_policy_controls_completed": True,
                      "actual_narrow_axis": narrow, "actual_rejections": len(rejected),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
