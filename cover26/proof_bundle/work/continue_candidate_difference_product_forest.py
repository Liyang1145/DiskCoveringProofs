"""Continue an UNADMITTED product forest without resetting any prior node.

The old diagnostic is preserved and fully rechecked arithmetically. This is
not a complete latest-source/model/geometry acceptance and pays zero roots.
"""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_difference_product_candidate_forest as forest
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_difference_product_curvature as numerical
import probe_candidate_positive_curvature_hull as fixed
import propose_candidate_difference_product_forest as initial
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=63)
    parser.add_argument("--depth", type=int, default=176)
    parser.add_argument("--parts", type=int, default=16)
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
        raise ValueError("product continuation changed fixed model/resource identity or scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("product continuation changed the actual same-root radius")
    seed_digest = binding.sha(args.seed)
    seed = binding.read(args.seed)
    if (seed["schema"] != "N26-unaccepted-fresh-root-difference-product-LOCAL-forest-diagnosis-v1"
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0
            or seed["executed_producer_sha256"] != binding.sha(initial.__file__)
            or seed["modules"][linux(Path(forest.__file__))] != binding.sha(forest.__file__)
            or seed["modules"][linux(Path(forest.product.__file__))] != binding.sha(forest.product.__file__)):
        raise ValueError("product continuation changed old unadmitted forest or exact arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("product continuation changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    if row != seed["actual_source_closed_box"]:
        raise ValueError("product continuation changed the entire actual source root")
    attempted = {item["source_OPEN_index"] for item in binding.read(
        args.source / "PROPOSAL.json")["forests"]}
    attempted.update(item["source_OPEN_index"] for item in binding.read(
        args.source / "SOURCE-ROOT-HISTORY.json"))
    if row["index"] in attempted:
        raise ValueError("product continuation would reset a formally accepted partial history")
    arcs = binding.force.load_trig(args.resource)[0]
    previous_result, previous_pending, previous_ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"])
    if (previous_result != seed["arithmetic_result"]
            or previous_pending != seed["pending_closed_leaf_boxes"]
            or previous_ledger != seed["arithmetic_ledger"]):
        raise ValueError("old product closed halves and every strict leaf did not reconstruct")
    print(json.dumps({"previous_arithmetic_forest_replayed": True,
                      "old_nodes": len(seed["nodes"]),
                      "retained_old_product_energy_leaves": previous_result["counts"]["PRODUCT-ENERGY"],
                      "old_OPEN_leaves": len(previous_pending),
                      "verified": False, "new_geometric_payments": 0}), flush=True)
    nodes = deepcopy(seed["nodes"])
    levels = {0: 0}
    for index, node in enumerate(nodes):
        if node["kind"] == "SPLIT":
            for child in node["children"]:
                levels[child] = levels[index] + 1
    queue = deque((leaf["index"], list(map(F, leaf["lower"])),
                   list(map(F, leaf["upper"])), levels[leaf["index"]])
                  for leaf in previous_pending)
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    reference = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])[0]
    root_box = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, c) in enumerate(zip(*root_box))
             if c - a <= F(1, 10**7)]
    free = [axis for axis in range(15) if axis not in tight]
    checks = 0
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        if nodes[index] != {"kind": "OPEN"}:
            raise ValueError("product continuation would overwrite a prior arithmetic payment")
        checks += 1
        box = tighten(original["matrix"], lower, upper)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        try:
            forest.original_forest.local_proof(original, lower, upper)
        except ValueError:
            pass
        else:
            nodes[index] = {"kind": "LOCAL"}
            continue
        certificate, _ = numerical.suggest(
            kernel, original["matrix"], reference, box, arcs, args.parts, tight)
        if certificate is not None:
            result = forest.product.bound(
                kernel, original["matrix"], lower, upper, certificate, original["radius"], arcs)
            if result["arithmetic_strict_target_test_passed"]:
                nodes[index] = {"kind": "PRODUCT-ENERGY", "certificate": certificate}
                continue
        if depth < args.depth:
            axis = max((axis for axis in free if lower[axis] < upper[axis]),
                       key=lambda axis: upper[axis] - lower[axis])
            cut = (lower[axis] + upper[axis]) / 2
            children = [len(nodes), len(nodes) + 1]
            nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
            nodes[index] = {"kind": "SPLIT", "axis": axis,
                            "mid": str(cut), "children": children}
            a, c = list(lower), list(upper)
            a[axis], c[axis] = cut, cut
            queue.extend((
                (children[0], list(lower), c, depth + 1),
                (children[1], a, list(upper), depth + 1)))
        if checks % 4 == 0:
            print(json.dumps({"new_checks": checks, "nodes": len(nodes),
                              "counts": {kind: sum(node["kind"] == kind for node in nodes)
                                         for kind in forest.KINDS},
                              "verified": False, "new_geometric_payments": 0}), flush=True)
    for index, old in enumerate(seed["nodes"]):
        if old["kind"] != "OPEN" and nodes[index] != old:
            raise AssertionError("product continuation changed a previous non-OPEN node")
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes)
    if (binding.sha(args.seed) != seed_digest
            or binding.sha(args.current_audit) != current_digest):
        raise ValueError("product old diagnostic or current snapshot changed during continuation")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during product continuation")
    report = {
        "schema": "N26-unaccepted-continued-root-difference-product-LOCAL-forest-diagnosis-v1",
        "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "old_unadmitted_forest_sha256": seed_digest,
        "old_unadmitted_forest_path": linux(args.seed),
        "all_previous_non_OPEN_nodes_preserved_identically": True,
        "actual_formal_source_partial_forests_DATA_not_reset": True,
        "nodes": nodes, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "new_diagnostic_checks": checks,
        "complete_latest_model_source_ownership_replay_NOT_performed": True,
        "new_product_mode_NOT_admitted_by_running_mixed_checker": True,
        "independent_product_geometry_acceptance_and_actual_current_join_still_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.product, numerical, codec, identity)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"diagnosis_completed": True, **result}), flush=True)


if __name__ == "__main__":
    main()
