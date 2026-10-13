"""Continue actual root25 v1 after its actual independent arithmetic tests."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_extended_signed_support_forest as forest
import n26_robust_positive_support_step as suggestion
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import propose_fresh_checked_positive_support_forest as previous_producer
import resume_support_cost_refined_forest as policy
import test_fresh_checked_positive_support_forest_arithmetic as previous_controls
import test_support_cost_split_policy as policy_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-preserved-fresh-root-support-cost-forest-continuation-v1"
BASE = forest.prior.prior


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed",
                 "arithmetic-controls", "policy-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=511)
    parser.add_argument("--depth", type=int, default=320)
    parser.add_argument("--max-supports", type=int, default=256)
    parser.add_argument("--existing-support-tries", type=int, default=6)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--iterations", type=int, default=220)
    parser.add_argument("--branch-policy", choices=("support-loss", "widest-all"), default="support-loss")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if (args.checks <= 0 or args.depth < 0
            or not 32 <= args.max_supports <= forest.MAX_SUPPORTS
            or not 1 <= args.existing_support_tries <= args.max_supports
            or not 1 <= args.rounds <= 4 or not 1 <= args.iterations <= 1000):
        raise ValueError("invalid preserved fresh-root continuation limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("fresh-root resume changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, controls = binding.read(args.seed), binding.read(args.arithmetic_controls)
    split_controls = binding.read(args.policy_controls)
    seed_digest, controls_digest = binding.sha(args.seed), binding.sha(args.arithmetic_controls)
    policy_digest = binding.sha(args.policy_controls)
    if (seed["schema"] != previous_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(previous_producer.__file__)
            or controls["schema"] != previous_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(previous_controls.__file__)
            or controls["diagnosis_sha256"] != seed_digest
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or controls["entire_actual_fresh_closed_root_partition_and_exact_ledger_reconstructed"] is not True
            or controls["source_actual_partial_forests_and_paid_leaves_NOT_reset"] is not True
            or controls["other_root_nodes_ownership_payments_and_acceptance_NOT_imported"] is not True
            or len(controls["actual_rejection_controls_passed"]) != 20
            or len(set(controls["actual_rejection_controls_passed"])) != 20
            or controls["independent_sine_square_feasible_corner_midpoint_checks"] !=
            3*controls["actual_strict_energy_leaves_independently_checked"]
            or controls["all_universal_positive_support_known_feasible_tiny_controls_passed"] !=
            len(seed["alternative_supports"])
            or split_controls["tested_producer_sha256"] != binding.sha(policy.__file__)
            or split_controls["executed_test_sha256"] != binding.sha(policy_controls.__file__)
            or split_controls["both_closed_halves_and_exact_shared_boundary_independently_reconstructed"] is not True
            or len(split_controls["invalid_policy_and_actual_shared_half_controls_rejected"]) != 8
            or split_controls["verified"] is not False or split_controls["new_geometric_payments"] != 0):
        raise ValueError("fresh-root resume lacks actual latest independent forest/policy controls")
    for module in (forest, forest.prior, forest.prior.signed):
        if (seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)
                or controls["tested_modules"][Path(module.__file__).name] != binding.sha(module.__file__)):
            raise ValueError("fresh-root resume changed exact original-rod arithmetic")
    current, current_digest = binding.read(args.current_audit), binding.sha(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("fresh-root resume changed actual same-root radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    if controls["source_file_sha256"] != seed["source_file_sha256"]:
        raise ValueError("fresh-root resume changed source/history DATA bindings")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("fresh-root resume changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    if (row != seed["actual_source_closed_box"] or row != controls["actual_source_closed_box"]
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0):
        raise ValueError("fresh-root resume changed actual target ownership or zero-payment scope")
    attempted = {item["source_OPEN_index"] for item in binding.read(args.source / "PROPOSAL.json")["forests"]}
    attempted.update(item["source_OPEN_index"] for item in binding.read(args.source / "SOURCE-ROOT-HISTORY.json"))
    if row["index"] in attempted:
        raise ValueError("diagnostic fresh-root resume would reset an actually owned source partial forest")
    arcs = binding.force.load_trig(args.resource)[0]
    old_result, old_pending, old_ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (old_result != seed["arithmetic_result"] or old_pending != seed["pending_closed_leaf_boxes"]
            or old_ledger != seed["arithmetic_ledger"]):
        raise ValueError("fresh-root resume failed entire actual checked-seed reconstruction")
    nodes, supports = deepcopy(seed["nodes"]), list(seed["alternative_supports"])
    if len(supports) > args.max_supports:
        raise ValueError("fresh-root continuation would truncate old checked supports")
    levels = {0: 0}
    for index, node in enumerate(nodes):
        if node["kind"] == "SPLIT":
            for child in node["children"]:
                levels[child] = levels[index]+1
    queue = deque((leaf["index"], list(map(F, leaf["lower"])), list(map(F, leaf["upper"])),
                   levels[leaf["index"]]) for leaf in old_pending)
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    local_reference = BASE.tighten(original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])[0]
    root_box = BASE.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    checks, alternations, appended, decisions = 0, 0, [], []
    print(json.dumps({"actual_checked_fresh_root_seed_fully_replayed": row["index"],
                      "old_nodes": len(nodes), "old_strict_leaves": len(old_ledger),
                      "old_OPEN_leaves": len(old_pending), "old_supports": len(supports),
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("fresh-root continuation would overwrite an old nonOPEN proof")
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
        node, data, rounds, added_round = suggestion.step(
            original, box, tight, arcs, supports, kernel, args.existing_support_tries,
            args.rounds, args.iterations, args.max_supports)
        alternations += rounds
        nodes[index] = node
        if added_round is not None:
            supports.append(data)
            appended.append({"actual_leaf_index": index, "round": added_round,
                             "new_support_index": node["support_index"]})
        if node["kind"] == "OPEN" and depth < args.depth:
            decision = policy.split_axis(lower, upper, data, args.branch_policy)
            if decision is not None:
                axis = decision["axis"]
                cut = (lower[axis]+upper[axis])/2
                children = [len(nodes), len(nodes)+1]
                nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": children}
                decisions.append({"node": index, "root_tight_axis_refined": axis in tight, **decision})
                left, right = list(upper), list(lower)
                left[axis], right[axis] = cut, cut
                queue.extend(((children[0], list(lower), left, depth+1),
                              (children[1], right, list(upper), depth+1)))
        if checks % 8 == 0:
            print(json.dumps({"actual_root": row["index"], "new_checks": checks, "nodes": len(nodes),
                              "NEW_signed_leaves": sum(node["kind"] == forest.KIND for node in nodes),
                              "OPEN_leaves": sum(node["kind"] == "OPEN" for node in nodes),
                              "positive_supports": len(supports),
                              "new_root_tight_axis_splits": sum(item["root_tight_axis_refined"] for item in decisions),
                              "verified": False, "new_geometric_payments": 0}), flush=True)
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    previous_controls.leaf_controls.previous.retention_gate(seed, {
        "nodes": nodes, "alternative_supports": supports, "arithmetic_ledger": ledger})
    for path, digest in ((args.seed, seed_digest), (args.arithmetic_controls, controls_digest),
                         (args.current_audit, current_digest), (args.policy_controls, policy_digest)):
        if binding.sha(path) != digest:
            raise ValueError("fresh-root seed/controls/current changed during continuation")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during fresh-root continuation")
    report = {
        "schema": SCHEMA, "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "old_arithmetic_forest_sha256": seed_digest, "old_arithmetic_forest_path": linux(args.seed),
        "actual_seed_independent_arithmetic_controls_sha256": controls_digest,
        "actual_split_policy_controls_sha256": policy_digest,
        "all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically": True,
        "all_previous_proved_closed_leaf_ledgers_preserved_identically": True,
        "source_actual_partial_forests_and_paid_leaves_NOT_reset": True,
        "borrowed_universal_support_data_sha256": seed["borrowed_universal_support_data_sha256"],
        "borrowed_support_independent_controls_sha256": seed["borrowed_support_independent_controls_sha256"],
        "other_root_nodes_ownership_payments_and_acceptance_NOT_imported": True,
        "nodes": nodes, "alternative_supports": supports,
        "arithmetic_result": result, "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "new_diagnostic_checks": checks, "weight_reference_alternation_rounds": alternations,
        "only_strict_useful_NEW_positive_supports_appended": appended,
        "new_split_decisions_DATA_only": decisions, "branch_policy": args.branch_policy,
        "all_nonzero_coordinate_axes_eligible_for_NEW_splits": True,
        "old_SPLIT_axes_and_closed_shared_boundaries_NOT_reset": True,
        "newest_forest_independent_arithmetic_controls_still_required": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.prior, forest.prior.signed, suggestion,
                                   codec, identity, previous_producer, previous_controls, policy)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"preserved_fresh_root_support_cost_continuation_completed": True,
                      "actual_root": row["index"], "nodes": len(nodes), "counts": result["counts"],
                      "retained_OPEN_leaves": len(pending),
                      "arithmetic_entire_root_lower_bound_cover_completed": not pending,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
