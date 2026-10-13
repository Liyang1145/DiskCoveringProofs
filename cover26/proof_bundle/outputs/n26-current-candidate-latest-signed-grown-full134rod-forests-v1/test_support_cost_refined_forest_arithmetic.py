"""Actual independent v6/v7 partitions, strict leaves and support-cost splits."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import resume_support_cost_refined_forest as producer
import test_checked_extended_robust_forest_arithmetic as old_controls
import test_support_cost_split_policy as policy_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-support-cost-refined-forest-arithmetic-controls-v1"


def split_decision_gate(original, row, seed, record):
    nodes = record["nodes"]
    decisions = record["new_split_decisions_DATA_only"]
    if (record["all_nonzero_coordinate_axes_eligible_for_NEW_splits"] is not True
            or record["old_SPLIT_axes_and_closed_shared_boundaries_NOT_reset"] is not True
            or record["branch_policy"] not in ("support-loss", "widest-all")
            or not isinstance(decisions, list)):
        raise ValueError("new support-cost forest changed explicit preserved split-policy scope")
    root_box = producer.BASE.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = {axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)}
    new_splits = {
        index for index, node in enumerate(nodes)
        if node["kind"] == "SPLIT" and
        (index >= len(seed["nodes"]) or seed["nodes"][index]["kind"] == "OPEN")
    }
    seen = set()
    for decision in decisions:
        index = decision["node"]
        if (type(index) is not int or index not in new_splits or index in seen
                or type(decision["axis"]) is not int
                or decision["axis"] != nodes[index]["axis"]
                or decision["root_tight_axis_refined"] != (decision["axis"] in tight)
                or decision["heuristic_selection_NOT_a_new_lower_bound_or_geometric_certificate"] is not True
                or F(decision["exact_coordinate_width"]) <= 0
                or decision["selection_reason"] not in (
                    "exact-negative-coordinate-support-contribution",
                    "widest-actual-coordinate-including-root-tight")):
            raise ValueError("new actual split-cost DATA omitted, duplicated or relabelled a closed split")
        seen.add(index)
        contribution = decision["exact_coordinate_contribution_DATA"]
        if (decision["selection_reason"] == "exact-negative-coordinate-support-contribution"
                and (type(contribution) is not str or F(contribution) >= 0)):
            raise ValueError("support-cost split DATA called a nonnegative contribution a strict loss")
    if seen != new_splits:
        raise ValueError("new support-cost forest hides an actual unreported split")
    return len(seen), sum(item["root_tight_axis_refined"] for item in decisions)


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "seed-controls",
                 "policy-controls", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("support-cost forest controls changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, record = binding.read(args.seed), binding.read(args.diagnosis)
    controls, policy = binding.read(args.seed_controls), binding.read(args.policy_controls)
    digests = {path: binding.sha(path) for path in
               (args.seed, args.seed_controls, args.policy_controls, args.diagnosis)}
    if (seed["schema"] != producer.previous_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(producer.previous_producer.__file__)
            or record["schema"] != producer.SCHEMA
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or record["old_arithmetic_forest_sha256"] != digests[args.seed]
            or record["actual_seed_independent_arithmetic_controls_sha256"] != digests[args.seed_controls]
            or record["all_previous_proved_closed_leaf_ledgers_preserved_identically"] is not True
            or controls["schema"] != old_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(old_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.seed]
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or len(controls["actual_rejection_controls_passed"]) != 20
            or policy["schema"] != "N26-support-cost-all-coordinate-split-policy-arithmetic-controls-v1"
            or policy["tested_producer_sha256"] != binding.sha(producer.__file__)
            or policy["executed_test_sha256"] != binding.sha(policy_controls.__file__)
            or len(policy["invalid_policy_and_actual_shared_half_controls_rejected"]) != 8
            or policy["both_closed_halves_and_exact_shared_boundary_independently_reconstructed"] is not True
            or policy["verified"] is not False or policy["new_geometric_payments"] != 0):
        raise ValueError("support-cost actual forest changed independent seed/policy or executor lineage")
    for data in (seed, record):
        for module in (forest, forest.prior, forest.prior.signed):
            if data["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
                raise ValueError("support-cost forest controls used changed exact leaf arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    if (record["source_file_sha256"] != seed["source_file_sha256"]
            or controls["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("support-cost forest controls changed actual source/history DATA bindings")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("support-cost forest controls changed actual source/root/history DATA")
    if policy["actual_source_root_DATA_sha256"] != seed["source_file_sha256"]["PENDING-ANGLES.json"]:
        raise ValueError("split-policy controls do not bind the actual unchanged source root table")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == record["source_OPEN_index"])
    for data in (seed, record):
        old_controls.previous.scope_gate(data, row)
    retained_nodes, retained_supports, retained_leaves = old_controls.previous.retention_gate(seed, record)
    arcs = binding.force.load_trig(args.resource)[0]
    old_controls.previous.reconstruct(original, kernel, arcs, row, seed, "v6-independent-seed")
    result, pending, ledger = old_controls.previous.reconstruct(
        original, kernel, arcs, row, record, "v7-support-cost-refined")
    energy, local, empty = old_controls.leaf_controls(original, kernel, arcs, record)
    negative = old_controls.previous.rejection_controls(original, kernel, arcs, row, seed, record)
    if len(negative) != 20:
        raise AssertionError("support-cost forest omitted a required actual arithmetic rejection")
    splits, narrow = split_decision_gate(original, row, seed, record)
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("actual support-cost input changed during independent arithmetic controls")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during support-cost forest controls")
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "seed_sha256": digests[args.seed], "seed_controls_sha256": digests[args.seed_controls],
        "policy_controls_sha256": digests[args.policy_controls], "diagnosis_sha256": digests[args.diagnosis],
        "both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed": True,
        "latest_arithmetic_result": result,
        "all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically": True,
        "old_nodes_retained": retained_nodes, "old_positive_supports_retained": retained_supports,
        "old_proved_closed_leaves_retained": retained_leaves,
        "actual_strict_energy_leaves_independently_checked": energy,
        "independent_sine_square_feasible_corner_midpoint_checks": energy*3,
        "actual_original_LOCAL_leaves_reconstructed_not_declared_empty": local,
        "actual_exact_EMPTY_leaves_reconstructed": empty,
        "actual_rejection_controls_passed": negative,
        "independently_tested_actual_split_policy_rejections": policy[
            "invalid_policy_and_actual_shared_half_controls_rejected"],
        "actual_new_closed_splits_and_shared_boundaries_reconstructed": splits,
        "new_actual_root_tight_coordinate_splits_checked": narrow,
        "support_cost_selection_DATA_NOT_a_proof_payment": True,
        "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "source_file_sha256": seed["source_file_sha256"],
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in (forest, forest.prior, forest.prior.signed,
                                          producer.BASE, codec, old_controls, producer, policy_controls)},
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_support_cost_refined_forest_independent_controls_completed": True,
                      "strict_energy_leaves": energy, "original_LOCAL_leaves": local,
                      "OPEN_leaves": len(pending), "actual_new_splits": splits,
                      "actual_new_root_tight_splits": narrow,
                      "actual_rejections": len(negative), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
