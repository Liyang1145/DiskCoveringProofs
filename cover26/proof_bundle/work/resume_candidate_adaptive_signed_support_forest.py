"""Resume an existing NEW signed forest; never reset old nodes or supports."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_candidate_adaptive_signed_support_forest as first_continuation
import n26_adaptive_signed_support_forest as forest
import n26_current_candidate_layer_identity as identity
import n26_typed_arithmetic_context as codec
import probe_alternative_signed_hull_forest as suggestion
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-continued-adaptive-NEW-signed-rod-support-forest-diagnosis-v1"


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=255)
    parser.add_argument("--depth", type=int, default=208)
    parser.add_argument("--existing-support-tries", type=int, default=8)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if args.checks <= 0 or args.depth < 0 or not 1 <= args.existing_support_tries <= 32:
        raise ValueError("adaptive signed resume limits are invalid")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("adaptive signed resume changed zero-source arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("adaptive signed resume changed actual same-root radius")
    seed, seed_digest = binding.read(args.seed), binding.sha(args.seed)
    allowed_producers = {binding.sha(first_continuation.__file__), binding.sha(__file__)}
    if (seed["schema"] != SCHEMA or seed["executed_producer_sha256"] not in allowed_producers
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0
            or seed["all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically"] is not True
            or seed["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True):
        raise ValueError("adaptive signed resume changed actual old diagnostic or admission scope")
    for module in (forest, forest.prior, forest.signed):
        if seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("adaptive signed resume changed old exact arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("adaptive signed resume changed actual source/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    if row != seed["actual_source_closed_box"]:
        raise ValueError("adaptive signed resume changed exact whole-root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    previous, old_pending, old_ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (previous != seed["arithmetic_result"] or old_pending != seed["pending_closed_leaf_boxes"]
            or old_ledger != seed["arithmetic_ledger"]):
        raise ValueError("all old adaptive signed nodes, supports and closed proofs did not reconstruct")
    print(json.dumps({
        "entire_previous_adaptive_signed_forest_replayed": True,
        "old_nodes": len(seed["nodes"]), "old_OPEN_leaves": len(old_pending),
        "all_previous_strict_nodes_and_supports_retained": True,
        "verified": False, "new_geometric_payments": 0}), flush=True)
    nodes, supports = deepcopy(seed["nodes"]), deepcopy(seed["alternative_supports"])
    levels = {0: 0}
    for index, node in enumerate(nodes):
        if node["kind"] == "SPLIT":
            for child in node["children"]:
                levels[child] = levels[index]+1
    queue = deque((leaf["index"], list(map(F, leaf["lower"])), list(map(F, leaf["upper"])),
                   levels[leaf["index"]]) for leaf in old_pending)
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    reference = forest.prior.tighten(original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])[0]
    root_box = forest.prior.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    free = [axis for axis in range(15) if axis not in tight]
    checks = 0
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("adaptive signed resume would overwrite an old non-OPEN proof")
        checks += 1
        box = forest.prior.tighten(original["matrix"], lower, upper)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        if max(max(abs(a-r), abs(b-r)) for a, b, r in zip(lower, upper, reference)) < F(1, 500000):
            try:
                forest.prior.local.local_proof(original, lower, upper)
            except ValueError:
                pass
            else:
                nodes[index] = {"kind": "LOCAL"}
                continue
        old = forest.prior.direct_bound(kernel, lower, upper, original["radius"], arcs)
        if old["radius_conditional_whole_angle_box_excluded"]:
            nodes[index] = {"kind": "ORIGINAL-ENERGY"}
            continue
        point = [(a+b)/2 for a, b in zip(lower, upper)]
        ordered = sorted(range(len(supports)), key=lambda support_index: sum(
            (float(a)-float(F(b)))**2 for a, b in zip(
                point, supports[support_index]["suggestion_point_turns"])))
        for support_index in ordered[:args.existing_support_tries]:
            certificate, diagnostic = suggestion.suggest(
                original, supports[support_index], box, point, tight, arcs)
            if (certificate is not None and diagnostic["exact_arithmetic_result"][
                    "arithmetic_strict_target_test_passed"]):
                nodes[index] = {
                    "kind": forest.KIND, "support_index": support_index, "certificate": certificate}
                break
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
            print(json.dumps({
                "new_checks": checks, "nodes": len(nodes),
                "counts": {kind: sum(node["kind"] == kind for node in nodes) for kind in forest.KINDS},
                "unchanged_old_positive_supports": len(supports),
                "verified": False, "new_geometric_payments": 0}), flush=True)
    if (supports != seed["alternative_supports"] or any(
            old["kind"] != "OPEN" and old != nodes[index] for index, old in enumerate(seed["nodes"]))):
        raise AssertionError("adaptive signed resume changed an old support or closed proof node")
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    if binding.sha(args.seed) != seed_digest or binding.sha(args.current_audit) != current_digest:
        raise ValueError("adaptive signed old forest or actual current snapshot changed during resume")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during adaptive signed resume")
    report = {
        "schema": SCHEMA, "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "old_arithmetic_forest_sha256": seed_digest,
        "old_arithmetic_forest_path": linux(args.seed),
        "all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically": True,
        "actual_formal_source_partial_forests_DATA_not_reset": True,
        "nodes": nodes, "alternative_supports": supports,
        "arithmetic_result": result, "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "new_diagnostic_checks": checks,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "NEW_signed_support_mode_NOT_admitted_by_running_mixed_or_product_checker": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.prior, forest.signed, codec, identity, suggestion)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "adaptive_NEW_signed_resume_completed": True, "nodes": result["nodes"], "counts": result["counts"],
        "retained_OPEN_leaves": len(pending),
        "arithmetic_entire_root_lower_bound_cover_completed":
            result["arithmetic_entire_root_lower_bound_cover_completed"],
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
