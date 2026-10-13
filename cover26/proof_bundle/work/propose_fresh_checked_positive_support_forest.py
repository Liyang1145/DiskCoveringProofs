"""Fresh actual root25 forest using independently checked universal rod DATA.

Weights on the SAME original rods can be retested on another actual angle
root. No other root's forest, ownership, paid leaf or acceptance is imported.
"""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_extended_robust_support_forest as support_producer
import n26_broad_positive_support_suggestion as broader
import n26_current_candidate_layer_identity as identity
import n26_extended_signed_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_robust_positive_support_references as robust
import test_checked_extended_robust_forest_arithmetic as support_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-fresh-root-checked-universal-positive-support-forest-v1"
BASE = forest.prior.prior


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "support-diagnosis", "support-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--index", type=int, default=25)
    parser.add_argument("--checks", type=int, default=127)
    parser.add_argument("--depth", type=int, default=208)
    parser.add_argument("--existing-support-tries", type=int, default=6)
    parser.add_argument("--max-supports", type=int, default=256)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--iterations", type=int, default=220)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if (args.checks <= 0 or args.depth < 0 or not 32 <= args.max_supports <= forest.MAX_SUPPORTS
            or not 1 <= args.existing_support_tries <= args.max_supports
            or not 1 <= args.rounds <= 4 or not 1 <= args.iterations <= 1000):
        raise ValueError("invalid fresh universal positive-support diagnostic limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("fresh support diagnosis changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    support_digest, controls_digest = binding.sha(args.support_diagnosis), binding.sha(args.support_controls)
    supplied, controls = binding.read(args.support_diagnosis), binding.read(args.support_controls)
    if (supplied["schema"] != support_producer.SCHEMA
            or supplied["executed_producer_sha256"] != binding.sha(support_producer.__file__)
            or controls["schema"] != support_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(support_controls.__file__)
            or controls["diagnosis_sha256"] != support_digest
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or controls["latest_arithmetic_result"] != supplied["arithmetic_result"]
            or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
            or len(controls["actual_rejection_controls_passed"]) != 20):
        raise ValueError("universal support DATA lacks actual independent newest arithmetic reconstruction")
    for module in (forest, forest.prior, forest.prior.signed):
        if (supplied["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__)
                or controls["tested_modules"][Path(module.__file__).name] != binding.sha(module.__file__)):
            raise ValueError("universal support DATA changed exact original-rod arithmetic")
    supports = supplied["alternative_supports"]
    borrowed_root = supplied["source_OPEN_index"]
    borrowed_count = len(supports)
    if args.index == borrowed_root or borrowed_count > args.max_supports:
        raise ValueError("fresh diagnostic would reset the donor root or truncate its checked support DATA")
    # No donor nodes, ledger, pending boxes, source ownership or payments enter
    # the target tree. Every universal weight/inverse is freshly checked below.
    del supplied
    forest.support_gate(original, supports)
    current, current_digest = binding.read(args.current_audit), binding.sha(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("fresh positive-support diagnosis changed actual same-root radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    source_files = ("PENDING-ANGLES.json", "PROPOSAL.json", "SOURCE-ROOT-HISTORY.json")
    digests = {name: binding.sha(args.source / name) for name in source_files}
    if any(accepted["files"][name] != digest for name, digest in digests.items()):
        raise ValueError("fresh positive-support diagnosis changed actual source/root/history DATA")
    attempted = {item["source_OPEN_index"] for item in binding.read(args.source / "PROPOSAL.json")["forests"]}
    attempted.update(item["source_OPEN_index"] for item in binding.read(args.source / "SOURCE-ROOT-HISTORY.json"))
    if args.index in attempted:
        raise ValueError("fresh diagnostic would reset an actual owned partial forest")
    selected = [row for row in binding.read(args.source / "PENDING-ANGLES.json") if row["index"] == args.index]
    if len(selected) != 1:
        raise ValueError("fresh support diagnosis requested a paid or nonexistent source root")
    row = selected[0]
    arcs = binding.force.load_trig(args.resource)[0]
    root_box = BASE.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    free = [axis for axis in range(15) if axis not in tight]
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    local_reference = BASE.tighten(original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])[0]
    nodes, queue = [{"kind": "OPEN"}], deque([(0, *root_box, 0)])
    checks, alternations, appended = 0, 0, []
    print(json.dumps({"fresh_actual_root": args.index, "borrowed_universal_support_DATA": borrowed_count,
                      "other_root_nodes_ownership_and_payments_NOT_imported": True,
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("fresh support diagnosis would overwrite a nonOPEN proof")
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
                                "certificate": deepcopy(trial["NEW_signed_certificate"])}
                appended.append({"actual_target_leaf": index, "round": round_index+1,
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
            print(json.dumps({"actual_root": args.index, "new_checks": checks, "nodes": len(nodes),
                              "NEW_signed_leaves": sum(node["kind"] == forest.KIND for node in nodes),
                              "OPEN_leaves": sum(node["kind"] == "OPEN" for node in nodes),
                              "positive_supports": len(supports), "verified": False,
                              "new_geometric_payments": 0}), flush=True)
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    if any(binding.sha(args.source / name) != digest for name, digest in digests.items()):
        raise ValueError("actual source/history DATA changed during fresh support diagnosis")
    for path, digest in ((args.current_audit, current_digest), (args.support_diagnosis, support_digest),
                         (args.support_controls, controls_digest)):
        if binding.sha(path) != digest:
            raise ValueError("completed current or universal support DATA changed during fresh diagnosis")
    report = {
        "schema": SCHEMA, "verified": False,
        "actual_current_audit_sha256": current_digest, "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": args.index, "actual_source_closed_box": row,
        "source_file_sha256": digests, "history_mode": "FRESH-DIAGNOSIS-ONLY",
        "source_actual_partial_forests_and_paid_leaves_NOT_reset": True,
        "borrowed_universal_support_data_sha256": support_digest,
        "borrowed_support_independent_controls_sha256": controls_digest,
        "borrowed_support_donor_root_index_DATA_only": borrowed_root,
        "borrowed_support_prefix_entries": borrowed_count,
        "other_root_nodes_ownership_payments_and_acceptance_NOT_imported": True,
        "all_universal_supports_freshly_checked_on_same_original_92_rods_and_new_weight_sums": True,
        "nodes": nodes, "alternative_supports": supports, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "new_diagnostic_checks": checks, "weight_reference_alternation_rounds": alternations,
        "only_strict_useful_NEW_positive_supports_appended": appended,
        "independent_actual_entire_newest_root_arithmetic_controls_still_required": True,
        "complete_latest_original_model_source_history_geometry_gate_NOT_performed": True,
        "new_mode_NOT_admitted_by_mixed_or_product_geometry_checker": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.prior, forest.prior.signed, robust, broader,
                                   codec, identity, support_controls, support_producer)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"fresh_checked_universal_support_forest_completed": True,
                      "actual_root": args.index, "nodes": len(nodes), "counts": result["counts"],
                      "retained_OPEN_leaves": len(pending), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
