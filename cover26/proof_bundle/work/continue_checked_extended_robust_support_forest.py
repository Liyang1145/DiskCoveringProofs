"""Continue v5 only after its actual independent arithmetic controls pass.

The historical forest and all its positive supports are retained. Additional
weight/reference alternations are numerical suggestions followed by exact
whole-closed-box tests; only useful strict new supports are appended.
"""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_broad_positive_support_suggestion as broader
import n26_current_candidate_layer_identity as identity
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_robust_positive_support_references as robust
import resume_extended_robust_support_forest as previous_producer
import test_extended_robust_support_forest_arithmetic as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-independently-checked-extended-robust-forest-continuation-v1"
BASE = forest.prior.prior


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "seed", "arithmetic-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=127)
    parser.add_argument("--depth", type=int, default=208)
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
        raise ValueError("invalid checked robust continuation limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("checked robust continuation changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, controls = binding.read(args.seed), binding.read(args.arithmetic_controls)
    seed_digest, controls_digest = binding.sha(args.seed), binding.sha(args.arithmetic_controls)
    if (seed["schema"] != previous_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(previous_producer.__file__)
            or controls["schema"] != independent.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(independent.__file__)
            or controls["diagnosis_sha256"] != seed_digest
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
            or controls["all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically"] is not True
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or len(controls["actual_rejection_controls_passed"]) != 20
            or len(set(controls["actual_rejection_controls_passed"])) != 20
            or controls["actual_strict_leaf_count_independently_tested"] != len(seed["arithmetic_ledger"])
            or controls["independent_sine_square_feasible_corner_midpoint_checks"] !=
            3*len(seed["arithmetic_ledger"])):
        raise ValueError("checked robust continuation lacks actual newest entire-forest arithmetic controls")
    for module in (forest, forest.prior, forest.prior.signed):
        if (seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)
                or controls["tested_modules"][Path(module.__file__).name] != binding.sha(module.__file__)):
            raise ValueError("checked robust continuation changed exact forest arithmetic")
    current, current_digest = binding.read(args.current_audit), binding.sha(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("checked robust continuation changed actual same-root radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    if controls["source_file_sha256"] != seed["source_file_sha256"]:
        raise ValueError("newest arithmetic controls changed actual source/history DATA bindings")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("checked robust continuation changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    independent.scope_gate(seed, row)
    if row != controls["actual_source_closed_box"]:
        raise ValueError("checked robust continuation changed exact whole-root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    previous, old_pending, old_ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (previous != seed["arithmetic_result"]
            or old_pending != seed["pending_closed_leaf_boxes"] or old_ledger != seed["arithmetic_ledger"]):
        raise ValueError("newest checked actual forest failed full reconstruction before continuing")
    nodes, supports = deepcopy(seed["nodes"]), list(seed["alternative_supports"])
    if len(supports) > args.max_supports:
        raise ValueError("explicit continuation table cap is below the unchanged historical prefix")
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
    free = [axis for axis in range(15) if axis not in tight]
    checks, alternations, appended = 0, 0, []
    print(json.dumps({"newest_independently_checked_forest_replayed": True,
                      "old_nodes": len(nodes), "old_strict_leaves": len(old_ledger),
                      "old_OPEN_leaves": len(old_pending), "old_supports": len(supports),
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("checked robust continuation would overwrite an old nonOPEN node")
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
                                "certificate": trial["NEW_signed_certificate"]}
                break
        for round_index in range(args.rounds):
            if nodes[index]["kind"] != "OPEN" or len(supports) >= args.max_supports:
                break
            best = None if not trials else max(trials, key=lambda trial: F(
                trial["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]["strict_radius_margin"]))
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
                                "certificate": trial["NEW_signed_certificate"]}
                appended.append({"actual_old_OPEN_leaf_index": index, "round": round_index+1,
                                 "new_support_index": support_index})
        if nodes[index]["kind"] == "OPEN":
            axes = [axis for axis in free if lower[axis] < upper[axis]]
            if depth < args.depth and axes:
                axis = max(axes, key=lambda axis: upper[axis]-lower[axis])
                cut = (lower[axis]+upper[axis])/2
                children = [len(nodes), len(nodes)+1]
                nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": children}
                left, right = list(upper), list(lower)
                left[axis], right[axis] = cut, cut
                queue.extend(((children[0], list(lower), left, depth+1),
                              (children[1], right, list(upper), depth+1)))
        if checks % 8 == 0:
            print(json.dumps({"new_checks": checks, "nodes": len(nodes),
                              "NEW_signed_leaves": sum(node["kind"] == forest.KIND for node in nodes),
                              "OPEN_leaves": sum(node["kind"] == "OPEN" for node in nodes),
                              "positive_supports": len(supports), "weight_reference_rounds": alternations,
                              "verified": False, "new_geometric_payments": 0}), flush=True)
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    independent.retention_gate(seed, {"nodes": nodes, "alternative_supports": supports,
                                     "arithmetic_ledger": ledger})
    for path, digest in ((args.seed, seed_digest), (args.arithmetic_controls, controls_digest),
                         (args.current_audit, current_digest)):
        if binding.sha(path) != digest:
            raise ValueError("checked robust seed/controls/current snapshot changed during continuation")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during checked robust continuation")
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
        "newest_forest_independent_arithmetic_controls_still_required": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.prior, forest.prior.signed, broader,
                                   codec, identity, robust, independent)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"checked_robust_extended_forest_continuation_completed": True,
                      "nodes": len(nodes), "counts": result["counts"],
                      "retained_OPEN_leaves": len(pending),
                      "arithmetic_entire_root_lower_bound_cover_completed": not pending,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
