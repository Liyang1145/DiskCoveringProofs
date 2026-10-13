"""Preserved root28 v7->v8 continuation after actual whole-forest controls."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_robust_positive_support_step as support_step
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import test_support_cost_refined_forest_arithmetic as previous
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-checked-preserved-support-cost-forest-continuation-v1"
forest = previous.forest
BASE = previous.producer.BASE


def data_gate(args):
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("checked support-cost continuation changed arithmetic model DATA")
    context = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = context["original"], context["original_kernel"]
    paths = (args.seed, args.seed_controls, args.policy_controls)
    digests = {path: binding.sha(path) for path in paths}
    seed, controls, policy = (binding.read(path) for path in paths)
    if (seed["schema"] != previous.producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(previous.producer.__file__)
            or controls["schema"] != previous.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(previous.__file__)
            or controls["diagnosis_sha256"] != digests[args.seed]
            or controls["policy_controls_sha256"] != digests[args.policy_controls]
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
            or controls["all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically"] is not True
            or len(controls["actual_rejection_controls_passed"]) != 20
            or len(controls["independently_tested_actual_split_policy_rejections"]) != 8
            or controls["independent_sine_square_feasible_corner_midpoint_checks"] !=
            3*controls["actual_strict_energy_leaves_independently_checked"]
            or seed["verified"] is not False or controls["verified"] is not False
            or seed["new_geometric_payments"] != 0 or controls["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0 or controls["candidate_whole_roots_removed"] != 0):
        raise ValueError("continuation lacks actual independently checked newest v7 seed")
    if (policy["schema"] != "N26-support-cost-all-coordinate-split-policy-arithmetic-controls-v1"
            or policy["tested_producer_sha256"] != binding.sha(previous.producer.__file__)
            or policy["executed_test_sha256"] != binding.sha(previous.policy_controls.__file__)
            or len(policy["invalid_policy_and_actual_shared_half_controls_rejected"]) != 8
            or policy["both_closed_halves_and_exact_shared_boundary_independently_reconstructed"] is not True
            or policy["verified"] is not False or policy["new_geometric_payments"] != 0):
        raise ValueError("continuation changed actual checked all-coordinate closed-split policy")
    for module in (forest, forest.prior, forest.prior.signed):
        if (seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)
                or controls["tested_modules"][Path(module.__file__).name] != binding.sha(module.__file__)):
            raise ValueError("checked continuation changed exact preserved leaf arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    if controls["source_file_sha256"] != seed["source_file_sha256"]:
        raise ValueError("checked continuation changed newest actual source/history DATA")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("checked continuation changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    previous.old_controls.previous.scope_gate(seed, row)
    if row != controls["actual_source_closed_box"] or row["index"] != 28:
        raise ValueError("checked root28 continuation imported another whole-root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    result, pending, ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (result != seed["arithmetic_result"] or pending != seed["pending_closed_leaf_boxes"]
            or ledger != seed["arithmetic_ledger"]):
        raise ValueError("checked continuation failed newest complete seed replay")
    return original, kernel, seed, controls, row, arcs, digests


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed",
                 "seed-controls", "policy-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=1023)
    parser.add_argument("--depth", type=int, default=384)
    parser.add_argument("--max-supports", type=int, default=256)
    parser.add_argument("--existing-support-tries", type=int, default=6)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--iterations", type=int, default=220)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if (args.checks <= 0 or args.depth < 0
            or not 32 <= args.max_supports <= forest.MAX_SUPPORTS
            or not 1 <= args.existing_support_tries <= args.max_supports
            or not 1 <= args.rounds <= 4 or not 1 <= args.iterations <= 1000):
        raise ValueError("invalid preserved continuation limits")
    original, kernel, seed, controls, row, arcs, digests = data_gate(args)
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("checked continuation changed same-root Rstar")
    module_digests = {linux(Path(module.__file__)): binding.sha(module.__file__)
                      for module in (forest, forest.prior, forest.prior.signed,
                                     support_step, previous, previous.producer,
                                     previous.policy_controls, codec, identity)}
    executed_digest = binding.sha(__file__)
    nodes, supports = deepcopy(seed["nodes"]), list(seed["alternative_supports"])
    if len(supports) > args.max_supports:
        raise ValueError("continuation would truncate the latest positive-support prefix")
    levels = {0: 0}
    for index, node in enumerate(nodes):
        if node["kind"] == "SPLIT":
            for child in node["children"]:
                levels[child] = levels[index]+1
    queue = deque((leaf["index"], list(map(F, leaf["lower"])), list(map(F, leaf["upper"])),
                   levels[leaf["index"]]) for leaf in seed["pending_closed_leaf_boxes"])
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    local_reference = BASE.tighten(original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])[0]
    root_box = BASE.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    checks, alternations, appended, decisions = 0, 0, [], []
    print(json.dumps({"latest_checked_v7_forest_fully_replayed": True,
                      "old_nodes": len(nodes), "old_strict_leaves": len(seed["arithmetic_ledger"]),
                      "old_OPEN_leaves": len(queue), "old_supports": len(supports),
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("checked continuation would overwrite a previous nonOPEN proof")
        checks += 1
        box = BASE.tighten(original["matrix"], lower, upper)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        if max(max(abs(a-r), abs(b-r)) for a, b, r in zip(lower, upper, local_reference)) < F(1, 500000):
            try:
                BASE.local.local_proof(original, lower, upper)
            except ValueError:
                pass
            else:
                nodes[index] = {"kind": "LOCAL"}
                continue
        if BASE.direct_bound(kernel, lower, upper, original["radius"], arcs)[
                "radius_conditional_whole_angle_box_excluded"]:
            nodes[index] = {"kind": "ORIGINAL-ENERGY"}
            continue
        leaf_node, supplemental, rounds, successful_round = support_step.step(
            original, box, tight, arcs, supports, kernel, args.existing_support_tries,
            args.rounds, args.iterations, args.max_supports)
        support = supplemental if leaf_node["kind"] == forest.KIND else None
        contributions = supplemental if leaf_node["kind"] == "OPEN" else None
        alternations += rounds
        nodes[index] = leaf_node
        if support is not None:
            if leaf_node["support_index"] != len(supports) or leaf_node["kind"] != forest.KIND:
                raise ValueError("useful fresh support does not belong to its actual strict leaf")
            supports.append(support)
            appended.append({"actual_leaf_index": index, "new_support_index": len(supports)-1,
                             "round": successful_round})
        if nodes[index]["kind"] == "OPEN" and depth < args.depth:
            decision = previous.producer.split_axis(lower, upper, contributions, "support-loss")
            if decision is not None:
                axis = decision["axis"]
                cut, children = (lower[axis]+upper[axis])/2, [len(nodes), len(nodes)+1]
                nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": children}
                decisions.append({"node": index, "root_tight_axis_refined": axis in tight, **decision})
                left, right = list(upper), list(lower)
                left[axis], right[axis] = cut, cut
                queue.extend(((children[0], list(lower), left, depth+1),
                              (children[1], right, list(upper), depth+1)))
        if checks % 8 == 0:
            print(json.dumps({"new_checks": checks, "nodes": len(nodes),
                              "NEW_signed_leaves": sum(node["kind"] == forest.KIND for node in nodes),
                              "OPEN_leaves": sum(node["kind"] == "OPEN" for node in nodes),
                              "positive_supports": len(supports),
                              "new_root_tight_axis_splits": sum(item["root_tight_axis_refined"] for item in decisions),
                              "verified": False, "new_geometric_payments": 0}), flush=True)
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    previous.old_controls.previous.retention_gate(seed, {
        "nodes": nodes, "alternative_supports": supports, "arithmetic_ledger": ledger})
    for path, digest in {**digests, args.current_audit: current_digest}.items():
        if binding.sha(path) != digest:
            raise ValueError("checked continuation input changed during arithmetic")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("checked continuation actual source/history changed")
    for path, digest in module_digests.items():
        if binding.sha(binding.local_path(path)) != digest:
            raise ValueError("checked continuation imported arithmetic changed during execution")
    if binding.sha(__file__) != executed_digest:
        raise ValueError("checked continuation producer changed during execution")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": row["index"],
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "actual_current_audit_sha256": current_digest, "actual_latest_candidate_layer_identity_only": layer,
        "old_arithmetic_forest_sha256": digests[args.seed],
        "actual_seed_independent_arithmetic_controls_sha256": digests[args.seed_controls],
        "actual_split_policy_controls_sha256": digests[args.policy_controls],
        "all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically": True,
        "all_previous_proved_closed_leaf_ledgers_preserved_identically": True,
        "actual_formal_source_partial_forests_DATA_not_reset": True,
        "nodes": nodes, "alternative_supports": supports, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "new_diagnostic_checks": checks, "weight_reference_alternation_rounds": alternations,
        "only_strict_useful_NEW_positive_supports_appended": appended,
        "new_split_decisions_DATA_only": decisions, "branch_policy": "support-loss",
        "all_nonzero_coordinate_axes_eligible_for_NEW_splits": True,
        "old_SPLIT_axes_and_closed_shared_boundaries_NOT_reset": True,
        "newest_forest_independent_arithmetic_controls_still_required": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_producer_sha256": executed_digest, "modules": module_digests,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"checked_preserved_support_cost_continuation_completed": True,
                      "nodes": len(nodes), "counts": result["counts"],
                      "retained_OPEN_leaves": len(pending), "entire_root_arithmetic_cover_completed": not pending,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
