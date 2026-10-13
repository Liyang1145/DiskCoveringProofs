"""Actual old OPEN-leaf supplements with a NEW full134rod exact kernel.

The running newest forest is not edited. No node, source ownership or proof
payment is replaced. All numerical values are suggestions, not proof.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from sympy import Matrix

from audit_prefix_partition import linux
import diagnose_candidate_full_face_rod_extension as model_producer
import n26_current_candidate_layer_identity as identity
import n26_full_candidate_face_energy as full
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_robust_positive_support_references as feasible
import propose_partial_stationary_energy as stationary
import test_candidate_full_face_rod_extension as model_controls
import test_checked_extended_robust_forest_arithmetic as seed_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-distinct-full134rod-candidate-leaf-energy-diagnosis-v1"


def float_energy(edges, weights, anchors):
    laplacian = np.zeros((76, 76))
    for (u, v), weight in zip(edges, weights):
        laplacian[u, u] += weight
        laplacian[v, v] += weight
        laplacian[u, v] -= weight
        laplacian[v, u] -= weight
    free = np.linalg.solve(laplacian[16:, 16:], -laplacian[16:, :16]@anchors)
    points = np.vstack((anchors, free))
    squared = np.array([np.dot(points[u]-points[v], points[u]-points[v]) for u, v in edges])
    return float(np.dot(weights, squared)), squared


def weight_suggestions(original, model, point, iterations):
    anchors = np.array([[np.cos(2*np.pi*float(turn)), np.sin(2*np.pi*float(turn))]
                        for turn in [F(0), *point]])
    old = np.array([float(F(int(value), int(original["reference"]["rational_scale"])))
                    for value in original["reference"]["weight_numerators"]])
    old /= old.sum()
    start = np.r_[old*.99, np.full(42, .01/42)]
    baseline, _ = float_energy(model["edges"], start, anchors)

    def logarithmic(shift):
        weights = start*np.exp(shift)
        weights /= weights.sum()
        value, squared = float_energy(model["edges"], weights, anchors)
        return -(value-baseline)*10**8, -weights*(squared-value)*10**8

    log_result = minimize(
        logarithmic, np.zeros(134), jac=True, method="L-BFGS-B",
        bounds=[(-3., 3.)]*134,
        options={"maxiter": iterations, "ftol": 1e-15, "gtol": 1e-9, "maxls": 50})
    log_weights = start*np.exp(log_result.x)
    log_weights /= log_weights.sum()
    cap = float(F(original["radius"])**2)

    def simplex(weights):
        value, squared = float_energy(model["edges"], weights, anchors)
        return -(value-cap*weights.sum())*1000, -(squared-cap)*1000

    floor = 1e-10
    initial = np.maximum(log_weights, floor)
    initial /= initial.sum()
    simplex_result = minimize(
        simplex, initial, jac=True, method="SLSQP",
        bounds=[(floor, 1.)]*134,
        constraints={"type": "eq", "fun": lambda weights: weights.sum()-1,
                     "jac": lambda weights: np.ones(134)},
        options={"maxiter": iterations, "ftol": 1e-13, "disp": False})
    weights = np.maximum(simplex_result.x, floor)
    weights /= weights.sum()
    return [
        ("full134-broader-log", log_weights, log_result),
        ("full134-positive-simplex", weights, simplex_result),
    ]


def exact_kernel(model, weights):
    scale = 10**30
    integers = [max(1, round(float(value)*scale)) for value in weights]
    laplacian = full.direct.laplacian(model["edges"], integers, vertices=76)
    inverse, denominator = Matrix([row[16:] for row in laplacian[16:]]).to_DM().inv_den()
    numbers = [[int(value) for value in row] for row in inverse.to_Matrix().tolist()]
    denominator = int(denominator)
    if denominator < 0:
        numbers, denominator = [[-value for value in row] for row in numbers], -denominator
    certificate = {
        "schema": full.SCHEMA, "mode": full.MODE, "weight_scale": scale,
        "weight_numerators": integers, "inverse_denominator": str(denominator),
        "inverse_numerators": [[str(value) for value in row] for row in numbers],
    }
    return certificate, full.kernel_gate(model, certificate)


def suggest_bound(original, kernel, box, reference, tight, arcs, parts):
    combined = full.combined_minorant(kernel, original["matrix"], reference, *box, arcs, parts)
    h = np.array([[float(value) for value in row] for row in combined])
    free = [axis for axis in range(15) if axis not in tight]
    minimum = float(np.linalg.eigvalsh(h[np.ix_(free, free)])[0])
    if minimum > 1e-10:
        beta = -F(max(1, int(minimum/4*10**12)), 10**12)
    else:
        beta = F(int((-minimum+max(1e-5, abs(minimum)/100))*10**12)+1, 10**12)
    shifted = h[np.ix_(free, free)]+float(beta)*np.eye(len(free))
    coupling = h[np.ix_(tight, free)]
    schur = h[np.ix_(tight, tight)]-coupling@np.linalg.solve(shifted, coupling.T)
    alpha = F(int((max(0., -float(np.linalg.eigvalsh(schur)[0]))*1.02+1)*10**8)+1, 10**8)
    for _ in range(6):
        certificate = {
            "reference_turns": list(map(str, reference)), "parts": parts,
            "signed_eta": [str(alpha if axis in tight else beta) for axis in range(15)],
            "difference_dual": {"q": 1, "terms": []},
        }
        try:
            result = full.bound(kernel, original["matrix"], *box, certificate, original["radius"], arcs)
        except ValueError:
            alpha = 2*alpha+1
        else:
            return certificate, result
    return None, None


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "model-diagnosis", "model-controls", "seed", "seed-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=1)
    parser.add_argument("--iterations", type=int, default=180)
    parser.add_argument("--parts", type=int, default=16)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if not 1 <= args.limit <= 4 or not 1 <= args.iterations <= 1000:
        raise ValueError("invalid small full134rod actual-leaf probe limits")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("full134rod probe changed fixed arithmetic model DATA identity")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    structural, controls = binding.read(args.model_diagnosis), binding.read(args.model_controls)
    model_digest, model_control_digest = binding.sha(args.model_diagnosis), binding.sha(args.model_controls)
    if (structural["schema"] != model_producer.SCHEMA
            or structural["executed_diagnostic_sha256"] != binding.sha(model_producer.__file__)
            or controls["schema"] != model_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(model_controls.__file__)
            or controls["diagnosis_sha256"] != model_digest
            or controls["independent_complete_native134rod_and_exact76vertex_bijection_checked"] is not True
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or len(controls["actual_independent_graph_scope_rejection_controls_passed"]) != 8):
        raise ValueError("full134rod probe lacks actual complete-face source/independent model controls")
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    if model["edges"] != structural["actual_structural_result"]["potential_NEW_allface_rod_edges_DATA"]:
        raise ValueError("new pure134rod model gate differs from the actual independent source structure")
    seed, seed_control = binding.read(args.seed), binding.read(args.seed_controls)
    seed_digest, seed_control_digest = binding.sha(args.seed), binding.sha(args.seed_controls)
    if (seed["schema"] != seed_controls.producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(seed_controls.producer.__file__)
            or seed_control["schema"] != seed_controls.SCHEMA
            or seed_control["executed_test_sha256"] != binding.sha(seed_controls.__file__)
            or seed_control["diagnosis_sha256"] != seed_digest
            or seed_control["latest_arithmetic_result"] != seed["arithmetic_result"]
            or seed_control["verified"] is not False or seed_control["new_geometric_payments"] != 0):
        raise ValueError("full134rod supplemental probe changed actual independently checked old leaf forest")
    if (structural["source_file_sha256"] != seed["source_file_sha256"]
            or controls["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("full134rod model/old-leaf DATA name different actual source or history bindings")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, expected in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != expected or accepted["files"][name] != expected:
            raise ValueError("full134rod probe changed actual source/root/history DATA")
    current, current_digest = binding.read(args.current_audit), binding.sha(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("full134rod probe changed actual same-root radius")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    seed_controls.previous.scope_gate(seed, row)
    arcs = binding.force.load_trig(args.resource)[0]
    tight = [axis for axis, (a, b) in enumerate(zip(row["sharp_lower"], row["sharp_upper"]))
             if F(b)-F(a) <= F(1, 10**7)]
    results = []
    for leaf in seed["pending_closed_leaf_boxes"][-args.limit:]:
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        point = [(a+b)/2 for a, b in zip(*box)]
        full.hull.quadratic.reference_gate(point, *box, original["matrix"])
        trials = []
        for name, weights, optimizer in weight_suggestions(original, model, point, args.iterations):
            certificate, kernel = exact_kernel(model, weights)
            identity_controls = full.native_graph.identity_control(kernel)
            if (kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
                    or kernel.get("alternative_positive_support_of_original_92_rods_NOT_original_fixed_weights") is not None):
                raise AssertionError("full134rod kernel forged an old92rod model flag")
            point_values = full.hull.quadratic.point_energy_gradient(kernel, [F(0), *point], arcs)
            point_cap = F(original["radius"])**2*F(sum(kernel["weights"]), kernel["scale"])
            angles, numerical = stationary.stationary(kernel, original["matrix"], *box, point)
            reference = feasible.feasible_reference(angles, *box, original["matrix"])
            energy_certificate, bound = suggest_bound(original, kernel, box, reference, tight, arcs, args.parts)
            tiny = original["cap"]["known_candidate_tiny_angle_cells"]
            tiny_result = full.direct.bound(
                [a for a, _ in tiny], [b for _, b in tiny], kernel, F(original["radius"])**2, arcs)
            if tiny_result["radius_conditional_whole_angle_box_excluded"]:
                raise AssertionError("NEW full134rod necessary energy excludes the known feasible tiny candidate")
            trial = {
                "strategy": name, "NEW_full134rod_kernel_certificate": certificate,
                "NEW_full134rod_exact_identity_controls": identity_controls,
                "actual_midpoint_turns": list(map(str, point)),
                "exact_midpoint_energy_lower": str(point_values[0]),
                "NEW_full134rod_same_root_energy_upper": str(point_cap),
                "exact_midpoint_strict_energy_margin": str(point_values[0]-point_cap),
                "NEW_full134rod_energy_certificate": energy_certificate,
                "NEW_full134rod_exact_closed_leaf_result": bound,
                "strict_actual_old_closed_leaf_exclusion": bound is not None and bound["arithmetic_strict_target_test_passed"],
                "known_feasible_tiny_original_same_root_control": tiny_result,
                "numerical_suggestions_NOT_proofs": {
                    "optimizer_success": bool(optimizer.success), "optimizer_message": str(optimizer.message),
                    "optimizer_iterations": int(optimizer.nit), **numerical},
            }
            trials.append(trial)
            print(json.dumps({
                "actual_old_leaf": leaf["index"], "strategy": name,
                "NEW_exact_ground_free_vertices": 60, "NEW_present_rods": 134,
                "strict_midpoint_arithmetic": point_values[0] > point_cap,
                "strict_whole_old_leaf": trial["strict_actual_old_closed_leaf_exclusion"],
                "verified": False, "new_geometric_payments": 0}), flush=True)
        results.append({"actual_old_OPEN_leaf": leaf, "trials": trials})
    for path, expected in ((args.model_diagnosis, model_digest), (args.model_controls, model_control_digest),
                           (args.seed, seed_digest), (args.seed_controls, seed_control_digest),
                           (args.current_audit, current_digest)):
        if binding.sha(path) != expected:
            raise ValueError("full134rod probe input DATA/current snapshot changed during arithmetic")
    for name, expected in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != expected:
            raise ValueError("actual source/history DATA changed during full134rod arithmetic")
    report = {
        "schema": SCHEMA, "verified": False,
        "actual_current_audit_sha256": current_digest, "actual_latest_candidate_layer_identity_only": layer,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "actual_allface_model_diagnosis_sha256": model_digest,
        "actual_allface_independent_controls_sha256": model_control_digest,
        "checked_old_leaf_forest_sha256": seed_digest, "checked_old_leaf_controls_sha256": seed_control_digest,
        "NEW_distinct_full134rod_edges": model["edges"], "results": results,
        "old92rod_original_kernel_weights_inverse_and_LOCAL_model_UNMODIFIED": True,
        "old_and_latest_running_forests_NOT_reset_or_relabelled": True,
        "successful_old_leaf_NEEDS_fresh_actual_newest_OPEN_descendant_reconstruction_before_reuse": True,
        "independent_actual_NEW60inverse_full134rod_energy_controls_still_required": True,
        "whole_actual_root_cover_NOT_proved": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (full, codec, identity, stationary, feasible, model_controls, seed_controls)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"NEW_distinct_full134rod_leaf_probe_completed": True, "actual_old_leaves": len(results),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
