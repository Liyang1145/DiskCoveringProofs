"""Zero-payment fresh-root product/LOCAL forest diagnosis on current row DATA."""

import argparse
from collections import deque
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
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--index", type=int, default=29)
    parser.add_argument("--checks", type=int, default=159)
    parser.add_argument("--depth", type=int, default=40)
    parser.add_argument("--parts", type=int, default=16)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if args.checks <= 0 or args.depth < 0:
        raise ValueError("product forest diagnostic limits invalid")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("product forest diagnosis changed resource/model identity or zero-source scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("product forest diagnosis changed the actual current radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    source_files = ("PENDING-ANGLES.json", "PROPOSAL.json", "SOURCE-ROOT-HISTORY.json")
    digests = {name: binding.sha(args.source / name) for name in source_files}
    if any(value != accepted["files"][name] for name, value in digests.items()):
        raise ValueError("product diagnostic changed actual source/root/history DATA")
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    selected = [row for row in incoming if row["index"] == args.index]
    if len(selected) != 1:
        raise ValueError("product diagnosis requested a paid/nonexistent actual root")
    attempted = {row["source_OPEN_index"] for row in binding.read(
        args.source / "PROPOSAL.json")["forests"]}
    attempted.update(row["source_OPEN_index"] for row in binding.read(
        args.source / "SOURCE-ROOT-HISTORY.json"))
    if args.index in attempted:
        raise ValueError("fresh product diagnostic would reset an accepted partial forest")
    row = selected[0]
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    ref = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])[0]
    arcs = binding.force.load_trig(args.resource)[0]
    root_box = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, c) in enumerate(zip(*root_box))
             if c - a <= F(1, 10**7)]
    free = [axis for axis in range(15) if axis not in tight]
    nodes = [{"kind": "OPEN"}]
    queue = deque([(0, *root_box, 0)])
    diagnoses, checks = [], 0
    while queue and checks < args.checks:
        index, lower, upper, level = queue.popleft()
        checks += 1
        box = tighten(original["matrix"], lower, upper)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        # The actual original LOCAL calculation, not this threshold, proves
        # LOCAL entry. The threshold only avoids costly hopeless attempts.
        if max(max(abs(a-r), abs(c-r)) for a, c, r in zip(lower, upper, ref)) < F(1, 500000):
            try:
                local = forest.original_forest.local_proof(original, lower, upper)
            except ValueError:
                pass
            else:
                nodes[index] = {"kind": "LOCAL"}
                diagnoses.append({"node": index, "kind": "LOCAL",
                                  "strict_entry_margin": local["strict_original_LOCAL_entry_margin"]})
                continue
        certificate, diagnostic = numerical.suggest(
            kernel, original["matrix"], ref, (lower, upper), arcs, args.parts, tight)
        if certificate is not None:
            check = forest.product.bound(
                kernel, original["matrix"], lower, upper, certificate, original["radius"], arcs)
            if check["arithmetic_strict_target_test_passed"]:
                nodes[index] = {"kind": "PRODUCT-ENERGY", "certificate": certificate}
                diagnoses.append({"node": index, "kind": "PRODUCT-ENERGY",
                                  "strict_energy_margin": check["strict_energy_margin"]})
                continue
        if level < args.depth:
            axes = [axis for axis in free if lower[axis] < upper[axis]]
            if axes:
                axis = max(axes, key=lambda axis: upper[axis] - lower[axis])
                cut = (lower[axis] + upper[axis]) / 2
                children = [len(nodes), len(nodes) + 1]
                nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                nodes[index] = {"kind": "SPLIT", "axis": axis,
                                "mid": str(cut), "children": children}
                left_upper, right_lower = list(upper), list(lower)
                left_upper[axis], right_lower[axis] = cut, cut
                queue.extend((
                    (children[0], list(lower), left_upper, level + 1),
                    (children[1], right_lower, list(upper), level + 1)))
        diagnoses.append({"node": index, "kind": nodes[index]["kind"],
                          "curvature_diagnosis": diagnostic})
        if checks % 8 == 0:
            print(json.dumps({
                "checked": checks, "nodes": len(nodes), "root": args.index,
                "counts": {kind: sum(node["kind"] == kind for node in nodes) for kind in forest.KINDS},
                "verified": False, "new_geometric_payments": 0}), flush=True)
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes)
    for name, digest in digests.items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("current source/history DATA changed during product forest diagnosis")
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("actual current snapshot changed during product forest diagnosis")
    report = {
        "schema": "N26-unaccepted-fresh-root-difference-product-LOCAL-forest-diagnosis-v1",
        "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "source_OPEN_index": args.index, "actual_source_closed_box": row,
        "source_accepted_partial_forests_DATA_not_reset": True,
        "history_mode": "FRESH-DIAGNOSIS-ONLY", "source_file_sha256": digests,
        "nodes": nodes, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "diagnostic_checks": checks, "node_diagnoses": diagnoses,
        "complete_latest_model_source_ownership_replay_NOT_performed": True,
        "new_product_mode_NOT_admitted_by_running_mixed_checker": True,
        "independent_product_partition_geometry_controls_acceptance_and_current_join_still_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.product, numerical, codec, identity)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"diagnosis_completed": True, "root": args.index, **result}), flush=True)


if __name__ == "__main__":
    main()
