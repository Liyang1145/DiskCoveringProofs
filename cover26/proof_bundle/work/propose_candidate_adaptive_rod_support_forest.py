"""Fresh zero-payment root forest using original and alternative positive rods."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from sympy import Matrix

from audit_prefix_partition import linux
import n26_adaptive_rod_support_forest as forest
import n26_current_candidate_layer_identity as identity
import n26_quadratic_energy_minorant as point_energy
import n26_typed_arithmetic_context as codec
import probe_candidate_difference_product_curvature as product_suggestion
import probe_candidate_positive_curvature_hull as fixed
import probe_candidate_reweighted_point_energy as numerical
import verify_conditional_force_stage as binding


def suggest_support(original, original_kernel, point, iterations):
    edges = original_kernel["edges"]
    anchors = np.array([[np.cos(2*np.pi*float(turn)), np.sin(2*np.pi*float(turn))]
                        for turn in [F(0), *point]])
    start = np.array(original_kernel["weights"], dtype=float)
    start /= start.sum()
    base, _ = numerical.float_energy(edges, start, anchors)

    def objective(shift):
        weights = start*np.exp(shift)
        weights /= weights.sum()
        value, squared = numerical.float_energy(edges, weights, anchors)
        return -(value-base)*10**8, -weights*(squared-value)*10**8

    suggestion = minimize(
        objective, np.zeros(92), jac=True, method="L-BFGS-B", bounds=[(-0.5, 0.5)]*92,
        options={"maxiter": iterations, "ftol": 1e-15, "gtol": 1e-9, "maxls": 40})
    weights = start*np.exp(suggestion.x)
    weights /= weights.sum()
    scale = 10**30
    integers = [max(1, round(float(weight)*scale)) for weight in weights]
    reference = deepcopy(original["reference"])
    reference.update(rational_scale=str(scale), weight_numerators=list(map(str, integers)),
                     alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=True)
    laplacian = forest.original_energy.laplacian(edges, integers)
    inverse, denominator = Matrix([row[16:] for row in laplacian[16:]]).to_DM().inv_den()
    integers_inverse = [[int(value) for value in row] for row in inverse.to_Matrix().tolist()]
    denominator = int(denominator)
    if denominator < 0:
        integers_inverse = [[-value for value in row] for row in integers_inverse]
        denominator = -denominator
    certificate = {
        "schema": "N26-exact-integer-ground-Dirichlet-inverse-v1", "anchor_vertices": 16,
        "inverse_denominator": str(denominator),
        "inverse_numerators": [[str(value) for value in row] for row in integers_inverse],
    }
    support = {"mode": "NEW-POSITIVE-SUPPORT", "reference": reference,
               "inverse": certificate, "suggestion_point_turns": list(map(str, point))}
    kernel = forest.alternative.kernel_gate(original["reference"], reference, certificate)
    return support, kernel, {
        "floating_optimizer_NOT_proof": True, "success": bool(suggestion.success),
        "iterations": int(suggestion.nit), "message": str(suggestion.message),
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "alternative-diagnosis", "alternative-controls", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--index", type=int, default=28)
    parser.add_argument("--checks", type=int, default=127)
    parser.add_argument("--depth", type=int, default=112)
    parser.add_argument("--parts", type=int, default=16)
    parser.add_argument("--max-supports", type=int, default=8)
    parser.add_argument("--support-window", default="1/100")
    parser.add_argument("--iterations", type=int, default=100)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if args.checks <= 0 or args.depth < 0 or not 1 <= args.max_supports <= 32:
        raise ValueError("adaptive rod support forest diagnostic limits are invalid")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("adaptive rod support diagnostic changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("adaptive support diagnosis changed actual same-root radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    source_files = ("PENDING-ANGLES.json", "PROPOSAL.json", "SOURCE-ROOT-HISTORY.json")
    digests = {name: binding.sha(args.source / name) for name in source_files}
    if any(digest != accepted["files"][name] for name, digest in digests.items()):
        raise ValueError("adaptive support diagnosis changed actual source/history DATA")
    selected = [row for row in binding.read(args.source / "PENDING-ANGLES.json")
                if row["index"] == args.index]
    if len(selected) != 1:
        raise ValueError("adaptive support diagnosis requested a paid or nonexistent source root")
    attempted = {row["source_OPEN_index"] for row in binding.read(
        args.source / "PROPOSAL.json")["forests"]}
    attempted.update(row["source_OPEN_index"] for row in binding.read(
        args.source / "SOURCE-ROOT-HISTORY.json"))
    if args.index in attempted:
        raise ValueError("fresh adaptive support forest would reset an accepted partial history")
    row = selected[0]
    diagnosis, controls = binding.read(args.alternative_diagnosis), binding.read(args.alternative_controls)
    if (diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["source_OPEN_index"] != args.index
            or diagnosis["actual_source_closed_box"] != row
            or controls["diagnosis_sha256"] != binding.sha(args.alternative_diagnosis)
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or len(controls["invalid_arithmetic_controls_rejected"]) != 12
            or controls["tested_alternative_module_sha256"] != binding.sha(forest.alternative.__file__)):
        raise ValueError("adaptive support diagnosis lost original tested alternative support")
    supports = [{
        "mode": "NEW-POSITIVE-SUPPORT", "reference": diagnosis["alternative_reference_DATA"],
        "inverse": diagnosis["alternative_exact_inverse_certificate"],
        "suggestion_point_turns": diagnosis["exact_point_turns"],
    }]
    support_kernels = forest.support_gate(original, supports)
    arcs = binding.force.load_trig(args.resource)[0]
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    reference = forest.tighten(original["matrix"], [a for a, _ in tiny], [b for _, b in tiny])[0]
    root_box = forest.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    free = [axis for axis in range(15) if axis not in tight]
    nodes = [{"kind": "OPEN"}]
    queue = deque([(0, *root_box, 0)])
    checks, new_support_diagnostics = 0, []
    while queue and checks < args.checks:
        index, lower, upper, depth = queue.popleft()
        checks += 1
        box = forest.tighten(original["matrix"], lower, upper)
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        if max(max(abs(a-r), abs(b-r)) for a, b, r in zip(lower, upper, reference)) < F(1, 500000):
            try:
                forest.local.local_proof(original, lower, upper)
            except ValueError:
                pass
            else:
                nodes[index] = {"kind": "LOCAL"}
                continue
        old = forest.direct_bound(kernel, lower, upper, original["radius"], arcs)
        if old["radius_conditional_whole_angle_box_excluded"]:
            nodes[index] = {"kind": "ORIGINAL-ENERGY"}
            continue
        for support_index, support_kernel in enumerate(support_kernels):
            result = forest.direct_bound(support_kernel, lower, upper, original["radius"], arcs)
            if result["radius_conditional_whole_angle_box_excluded"]:
                nodes[index] = {"kind": "ALTERNATIVE-ENERGY", "support_index": support_index}
                break
        if nodes[index]["kind"] != "OPEN":
            continue
        certificate, _ = product_suggestion.suggest(
            kernel, original["matrix"], reference, box, arcs, args.parts, tight)
        if certificate is not None:
            result = forest.product.bound(
                kernel, original["matrix"], lower, upper, certificate, original["radius"], arcs)
            if result["arithmetic_strict_target_test_passed"]:
                nodes[index] = {"kind": "PRODUCT-ENERGY", "certificate": certificate}
                continue
        if (len(supports) < args.max_supports
                and max(b-a for a, b in zip(lower, upper)) <= F(args.support_window)):
            point = [(a+b)/2 for a, b in zip(lower, upper)]
            point_energy.reference_gate(point, lower, upper, original["matrix"])
            support, support_kernel, numerical_record = suggest_support(
                original, kernel, point, args.iterations)
            support_index = len(supports)
            supports.append(support)
            support_kernels.append(support_kernel)
            result = forest.direct_bound(support_kernel, lower, upper, original["radius"], arcs)
            new_support_diagnostics.append({
                "node": index, "support_index": support_index, **numerical_record,
                "exact_target_closed_box_strictly_excluded":
                    result["radius_conditional_whole_angle_box_excluded"]})
            print(json.dumps({
                "fresh_exact_positive_support_added": support_index,
                "whole_closed_leaf_arithmetically_excluded":
                    result["radius_conditional_whole_angle_box_excluded"],
                "verified": False, "new_geometric_payments": 0}), flush=True)
            if result["radius_conditional_whole_angle_box_excluded"]:
                nodes[index] = {"kind": "ALTERNATIVE-ENERGY", "support_index": support_index}
                continue
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
                "checked": checks, "nodes": len(nodes),
                "counts": {kind: sum(node["kind"] == kind for node in nodes) for kind in forest.KINDS},
                "positive_supports": len(supports),
                "verified": False, "new_geometric_payments": 0}), flush=True)
    result, pending, ledger = forest.replay(original, kernel, arcs, row, nodes, supports)
    for name, digest in digests.items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during adaptive support discovery")
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("actual current snapshot changed during adaptive support discovery")
    report = {
        "schema": "N26-unaccepted-fresh-adaptive-original-rod-support-forest-diagnosis-v1",
        "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "source_OPEN_index": args.index, "actual_source_closed_box": row,
        "source_file_sha256": digests,
        "actual_formal_source_partial_forests_DATA_not_reset": True,
        "nodes": nodes, "alternative_supports": supports,
        "arithmetic_result": result, "pending_closed_leaf_boxes": pending,
        "arithmetic_ledger": ledger, "diagnostic_checks": checks,
        "new_support_suggestion_diagnostics": new_support_diagnostics,
        "initial_alternative_diagnosis_sha256": binding.sha(args.alternative_diagnosis),
        "initial_alternative_controls_sha256": binding.sha(args.alternative_controls),
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_alternative_support_mode_NOT_supported_by_running_mixed_or_tested_product_checker": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_producer_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, forest.alternative, forest.product, codec,
                                   identity, product_suggestion, numerical)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"adaptive_support_diagnosis_completed": True, **result}), flush=True)


if __name__ == "__main__":
    main()
