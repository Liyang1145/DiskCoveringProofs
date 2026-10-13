"""Preserved v6 continuation guided by exact support-loss DATA, not a proof.

Every nonzero coordinate is eligible for a new closed split. Historical
SPLITs, proved leaves and the entire positive-support prefix remain unchanged.
The arithmetic backend, radius, model and proof modes are not modified.
"""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_extended_robust_support_forest as previous_producer
import n26_broad_positive_support_suggestion as broader
import n26_current_candidate_layer_identity as identity
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_robust_positive_support_references as robust
import test_checked_extended_robust_forest_arithmetic as previous_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-preserved-support-cost-refined-forest-diagnosis-v1"
BASE = forest.prior.prior


def split_axis(lower, upper, contributions, policy):
    if (len(lower) != 15 or len(upper) != 15
            or any(a > b for a, b in zip(lower, upper))
            or policy not in ("support-loss", "widest-all")):
        raise ValueError("invalid support-cost split domain or policy")
    eligible = [axis for axis in range(15) if lower[axis] < upper[axis]]
    if not eligible:
        return None
    if contributions is not None:
        if (not isinstance(contributions, list) or len(contributions) != 15
                or any(type(value) is not str for value in contributions)):
            raise ValueError("support-cost split has malformed exact coordinate contributions")
        costs = list(map(F, contributions))
    else:
        costs = None
    negative = [] if costs is None else [axis for axis in eligible if costs[axis] < 0]
    if policy == "support-loss" and negative:
        axis = min(negative, key=lambda axis: (costs[axis], -(upper[axis]-lower[axis]), axis))
        reason = "exact-negative-coordinate-support-contribution"
    else:
        axis = max(eligible, key=lambda axis: (upper[axis]-lower[axis], -axis))
        reason = "widest-actual-coordinate-including-root-tight"
    return {
        "axis": axis, "selection_reason": reason,
        "exact_coordinate_contribution_DATA": None if costs is None else str(costs[axis]),
        "exact_coordinate_width": str(upper[axis]-lower[axis]),
        "heuristic_selection_NOT_a_new_lower_bound_or_geometric_certificate": True,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "seed", "arithmetic-controls", "report"):
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
        raise ValueError("invalid support-cost preserved-forest limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("support-cost resume changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, controls = binding.read(args.seed), binding.read(args.arithmetic_controls)
    seed_digest, controls_digest = binding.sha(args.seed), binding.sha(args.arithmetic_controls)
    if (seed["schema"] != previous_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(previous_producer.__file__)
            or controls["schema"] != previous_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(previous_controls.__file__)
            or controls["diagnosis_sha256"] != seed_digest
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
            or controls["all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically"] is not True
            or len(controls["actual_rejection_controls_passed"]) != 20
            or len(set(controls["actual_rejection_controls_passed"])) != 20
            or controls["independent_sine_square_feasible_corner_midpoint_checks"] !=
            3*controls["actual_strict_energy_leaves_independently_checked"]):
        raise ValueError("support-cost resume lacks actual latest v6 independent arithmetic controls")
    for module in (forest, forest.prior, forest.prior.signed):
        if (seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)
                or controls["tested_modules"][Path(module.__file__).name] != binding.sha(module.__file__)):
            raise ValueError("support-cost resume changed exact original-rod forest arithmetic")
    current, current_digest = binding.read(args.current_audit), binding.sha(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("support-cost resume changed actual same-root radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    if controls["source_file_sha256"] != seed["source_file_sha256"]:
        raise ValueError("support-cost resume changed exact source/history DATA bindings")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("support-cost resume changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    previous_controls.previous.scope_gate(seed, row)
    if row != controls["actual_source_closed_box"]:
        raise ValueError("support-cost resume changed actual whole-root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    old_result, old_pending, old_ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (old_result != seed["arithmetic_result"] or old_pending != seed["pending_closed_leaf_boxes"]
            or old_ledger != seed["arithmetic_ledger"]):
        raise ValueError("support-cost resume failed newest full checked-forest reconstruction")
    nodes, supports = deepcopy(seed["nodes"]), list(seed["alternative_supports"])
    if len(supports) > args.max_supports:
        raise ValueError("support-cost table limit would truncate old checked supports")
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
    print(json.dumps({"latest_checked_v6_forest_fully_replayed": True,
                      "old_nodes": len(nodes), "old_strict_leaves": len(old_ledger),
                      "old_OPEN_leaves": len(old_pending), "old_supports": len(supports),
                      "all_nonzero_coordinate_axes_eligible_for_NEW_splits": True,
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("support-cost resume would overwrite a previous nonOPEN proof")
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
        direct = BASE.direct_bound(kernel, lower, upper, original["radius"], arcs)
        if direct["radius_conditional_whole_angle_box_excluded"]:
            nodes[index] = {"kind": "ORIGINAL-ENERGY"}
            continue
        center = [(a+b)/2 for a, b in zip(lower, upper)]
        ordered = sorted(range(len(supports)), key=lambda support_index: sum(
            (float(a)-float(F(b)))**2 for a, b in zip(
                center, supports[support_index]["suggestion_point_turns"])))
        trials = []
        for support_index in ordered[:args.existing_support_tries]:
            trial = robust.test_reference(original, supports[support_index], box, center, tight, arcs)
            if trial["NEW_signed_certificate"] is not None:
                trials.append(trial)
            if trial["strict_actual_closed_leaf_exclusion"]:
                nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                                "certificate": deepcopy(trial["NEW_signed_certificate"])}
                break
        for round_index in range(args.rounds):
            if nodes[index]["kind"] != "OPEN" or len(supports) >= args.max_supports:
                break
            best = None if not trials else max(trials, key=lambda item: F(
                item["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]["strict_radius_margin"]))
            reference = center if best is None else list(map(F, best["reference_turns"]))
            alternations += 1
            strict = []
            for support, _, _ in broader.suggest(original, kernel, reference, args.iterations, 3):
                trial = robust.test_reference(original, support, box, reference, tight, arcs)
                if trial["NEW_signed_certificate"] is not None:
                    trials.append(trial)
                if trial["strict_actual_closed_leaf_exclusion"]:
                    strict.append(trial)
            if strict:
                trial = max(strict, key=lambda item: F(item["signed_arithmetic_diagnosis"][
                    "exact_arithmetic_result"]["strict_radius_margin"]))
                support_index = len(supports)
                supports.append(trial["NEW_positive_support"])
                nodes[index] = {"kind": forest.KIND, "support_index": support_index,
                                "certificate": deepcopy(trial["NEW_signed_certificate"])}
                appended.append({"actual_leaf_index": index, "round": round_index+1,
                                 "new_support_index": support_index})
        if nodes[index]["kind"] == "OPEN" and depth < args.depth:
            best = None if not trials else max(trials, key=lambda item: F(
                item["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]["strict_radius_margin"]))
            contributions = None if best is None else best["signed_arithmetic_diagnosis"][
                "exact_arithmetic_result"]["coordinate_contributions"]
            decision = split_axis(lower, upper, contributions, args.branch_policy)
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
            print(json.dumps({"new_checks": checks, "nodes": len(nodes),
                              "NEW_signed_leaves": sum(node["kind"] == forest.KIND for node in nodes),
                              "OPEN_leaves": sum(node["kind"] == "OPEN" for node in nodes),
                              "positive_supports": len(supports),
                              "new_root_tight_axis_splits": sum(item["root_tight_axis_refined"] for item in decisions),
                              "verified": False, "new_geometric_payments": 0}), flush=True)
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    previous_controls.previous.retention_gate(seed, {
        "nodes": nodes, "alternative_supports": supports, "arithmetic_ledger": ledger})
    for path, digest in ((args.seed, seed_digest), (args.arithmetic_controls, controls_digest),
                         (args.current_audit, current_digest)):
        if binding.sha(path) != digest:
            raise ValueError("support-cost seed/controls/current changed during exact continuation")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during support-cost continuation")
    report = {
        "schema": SCHEMA, "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "old_arithmetic_forest_sha256": seed_digest, "old_arithmetic_forest_path": linux(args.seed),
        "actual_seed_independent_arithmetic_controls_sha256": controls_digest,
        "all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically": True,
        "all_previous_proved_closed_leaf_ledgers_preserved_identically": True,
        "actual_formal_source_partial_forests_DATA_not_reset": True,
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
                    for module in (forest, forest.prior, forest.prior.signed, broader,
                                   codec, identity, robust, previous_producer, previous_controls)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"preserved_support_cost_refined_forest_completed": True,
                      "nodes": len(nodes), "counts": result["counts"],
                      "retained_OPEN_leaves": len(pending),
                      "arithmetic_entire_root_lower_bound_cover_completed": not pending,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
