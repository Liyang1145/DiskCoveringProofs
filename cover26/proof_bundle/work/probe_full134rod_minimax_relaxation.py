"""Fullface fixed-anchor minimax DATA, exact points and fresh stress proposals.

Distance-model realizations are NOT disk covers. Numerical primal/dual
values are suggestions; only explicitly reconstructed exact results count.
No old or currently running forest is changed.
"""

import argparse
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path

import numpy as np
from scipy.optimize import lsq_linear, minimize

from audit_prefix_partition import linux
import probe_full134rod_correlated_support as prior_producer
import test_full134rod_correlated_support as prior_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-full134rod-fixed-anchor-minimax-relaxation-diagnosis-v1"
full = prior_producer.correlated.full


def minimax_suggestion(model, kernel, turns, iterations):
    anchors = np.array([[np.cos(2*np.pi*float(t)), np.sin(2*np.pi*float(t))]
                        for t in [F(0), *turns]])
    harmonic = np.array([[float(F(value, kernel["inverse_denominator"])) for value in row]
                         for row in kernel["harmonic"]])
    initial_points = harmonic@anchors
    edges = model["edges"]

    def positions(x):
        return np.vstack((anchors, x[:120].reshape(60, 2)))

    def rod_values(x):
        points = positions(x)
        return np.array([np.dot(points[u]-points[v], points[u]-points[v]) for u, v in edges])

    def constraint(x):
        points = positions(x)
        rods = rod_values(x)
        free = points[16:]
        return np.r_[x[-1]-rods, 1-np.einsum("ij,ij->i", free, free)]

    def jacobian(x):
        points = positions(x)
        jac = np.zeros((194, 121))
        for index, (u, v) in enumerate(edges):
            difference = points[u]-points[v]
            if u >= 16:
                jac[index, 2*(u-16):2*(u-16)+2] -= 2*difference
            if v >= 16:
                jac[index, 2*(v-16):2*(v-16)+2] += 2*difference
            jac[index, -1] = 1
        for index, point in enumerate(points[16:]):
            jac[134+index, 2*index:2*index+2] = -2*point
        return jac

    initial = np.r_[initial_points.ravel(), 1.]
    initial[-1] = float(max(rod_values(initial)))+1e-5
    objective_scale = 10**5
    derivative = np.r_[np.zeros(120), objective_scale]
    optimized = minimize(
        lambda x: float(x[-1]*objective_scale), initial, jac=lambda x: derivative,
        method="SLSQP", bounds=[(-1., 1.)]*120+[(0., 1.)],
        constraints={"type": "ineq", "fun": constraint, "jac": jacobian},
        options={"ftol": 1e-12, "maxiter": iterations, "disp": False})
    if not np.all(np.isfinite(optimized.x)):
        raise ValueError("full134rod minimax returned a nonfinite numerical suggestion")
    points = positions(optimized.x)
    squared = rod_values(optimized.x)
    # Recover nonnegative stress suggestions from approximate free equilibrium,
    # rather than declaring an optimizer multiplier to be an exact proof.
    equilibrium = -jacobian(optimized.x)[:134, :120].T
    gap = max(squared)-squared
    active = gap <= 1e-7
    upper = np.where(active, 1., 1e-8)
    matrix = np.vstack((equilibrium, np.ones(134)))
    rhs = np.r_[np.zeros(120), 1.]
    stress = lsq_linear(matrix, rhs, bounds=(np.full(134, 1e-12), upper),
                       method="trf", tol=1e-12, max_iter=iterations)
    weights = np.maximum(stress.x, 1e-12)
    weights /= weights.sum()
    return points[16:], weights, {
        "numerical_convex_minimax_success_NOT_proof": bool(optimized.success),
        "numerical_convex_minimax_message": str(optimized.message),
        "numerical_convex_minimax_iterations": int(optimized.nit),
        "numerical_max_squared_rod_NOT_a_radius_certificate": float(max(squared)),
        "numerical_active_rod_count_DATA": int(active.sum()),
        "numerical_nonnegative_stress_fit_success_NOT_proof": bool(stress.success),
        "numerical_free_equilibrium_residual_NOT_proof": float(np.max(np.abs(equilibrium@weights))),
    }


def exact_relaxation(model, matrix, leaf, turns, free_points, radius_lower, arcs):
    if (len(turns) != 15 or len(free_points) != 60 or any(len(point) != 2 for point in free_points)):
        raise ValueError("full134rod exact relaxation has a wrong frame or free dimension")
    full.hull.quadratic.reference_gate(turns, leaf["lower"], leaf["upper"], matrix)
    positions = []
    for turn in [F(0), *map(F, turns)]:
        cosine, sine = arcs.sincos_turn(turn)
        positions.append([(F(a, arcs.SCALE), F(b, arcs.SCALE)) for a, b in (cosine, sine)])
    free = [list(map(F, point)) for point in free_points]
    positions.extend([[(value, value) for value in point] for point in free])
    squared = []
    for u, v in model["edges"]:
        upper = F(0)
        for (a, b), (c, d) in zip(positions[u], positions[v]):
            upper += max((a-d)**2, (b-c)**2)
        squared.append(upper)
    maximum, grid = max(squared), 10**12
    integer = isqrt(maximum.numerator*grid**2//maximum.denominator)
    if F(integer, grid)**2 < maximum:
        integer += 1
    radius = F(integer+1, grid)
    margins = [radius**2-value for value in squared]
    norms = [1-x*x-y*y for x, y in free]
    if not min(margins) > 0:
        raise AssertionError("outward minimax relaxation radius did not cover all actual134rods")
    below = radius < F(radius_lower) and min(norms) >= 0
    return {
        "exact_all134rod_distance_upper_bounds": list(map(str, squared)),
        "exact_outward_realization_radius": str(radius),
        "exact_minimum_all134rod_squared_distance_margin": str(min(margins)),
        "all60_free_centers_and_face_witnesses_inside_unit_disk": min(norms) >= 0,
        "exact_minimum_all60_free_unit_disk_margin": str(min(norms)),
        "exact_radius_margin_below_candidate_Rstar_LOWER": str(F(radius_lower)-radius),
        "exact_below_Rstar_complete134rod_NECESSARY_model_realization": below,
        "continuous_unit_disk_cover_NOT_proved": True,
        "embedding_and_topological_cover_constraints_NOT_accepted": True,
        "not_a_global_optimality_counterexample": True,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "correlated-diagnosis", "correlated-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=400)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if not 1 <= args.iterations <= 1000:
        raise ValueError("invalid small fullface minimax probe iteration count")
    original, model, seed, ancestor, prior, row, arcs, digests, layer = prior_producer.input_gate(args)
    correlation = binding.read(args.correlated_diagnosis)
    controls = binding.read(args.correlated_controls)
    digests[args.correlated_diagnosis] = binding.sha(args.correlated_diagnosis)
    digests[args.correlated_controls] = binding.sha(args.correlated_controls)
    if (correlation["schema"] != prior_producer.SCHEMA
            or correlation["executed_probe_sha256"] != binding.sha(prior_producer.__file__)
            or correlation["checked_v7_forest_sha256"] != digests[args.seed]
            or correlation["source_file_sha256"] != seed["source_file_sha256"]
            or controls["schema"] != prior_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(prior_controls.__file__)
            or controls["tested_correlated_module_sha256"] != binding.sha(prior_producer.correlated.__file__)
            or controls["diagnosis_sha256"] != digests[args.correlated_diagnosis]
            or len(controls["actual_correlated_mode_rejection_controls_passed"]) != 24
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0):
        raise ValueError("minimax probe lacks actual independent correlated/fullface controls")
    latest = {item["actual_newest_OPEN_leaf"]["index"]: item for item in prior["results"]}
    radius_lower = binding.read(args.current_audit)["r_strict_interval"][0]
    results = []
    for item in correlation["results"]:
        leaf = item["actual_checked_v7_OPEN_leaf"]
        if leaf != latest[leaf["index"]]["actual_newest_OPEN_leaf"]:
            raise ValueError("minimax probe changed actual checked old whole OPEN leaf")
        trial = max(item["trials"], key=lambda trial: F(
            trial["NEW_correlated_exact_closed_leaf_result"]["strict_radius_margin"]))
        turns = trial["NEW_correlated_quadratic_certificate"]["reference_turns"]
        kernel, _ = prior_producer.previous.arithmetic.kernel_controls(
            model, trial["NEW_full134rod_kernel_certificate"])
        points, weights, numerical = minimax_suggestion(model, kernel, list(map(F, turns)), args.iterations)
        rational = [[str(F(round(float(value)*10**16), 10**16)) for value in point] for point in points]
        exact = exact_relaxation(model, original["matrix"], leaf, turns, rational,
                                 radius_lower, arcs)
        stress_certificate, stress_kernel = prior_producer.previous.producer.old_probe.exact_kernel(model, weights)
        stress_identity = full.native_graph.identity_control(stress_kernel)
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        root_box = prior_producer.previous.producer.latest_controls.producer.BASE.tighten(
            original["matrix"], row["sharp_lower"], row["sharp_upper"])
        tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
        old_certificate, old_result = prior_producer.previous.producer.old_probe.suggest_bound(
            original, stress_kernel, box, list(map(F, turns)), tight, arcs, 16)
        certificate, result, bound_suggestion = (None, None, None)
        if old_certificate is not None:
            certificate, result, bound_suggestion = prior_producer.suggest(
                stress_kernel, original, leaf, old_certificate, arcs)
        tiny = original["cap"]["known_candidate_tiny_angle_cells"]
        tiny_result = full.direct.bound(
            [a for a, _ in tiny], [b for _, b in tiny], stress_kernel, F(original["radius"])**2, arcs)
        if tiny_result["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("fresh minimax stress excludes known feasible tiny candidate")
        results.append({
            "actual_checked_v7_OPEN_leaf": leaf,
            "actual_fixed_feasible_anchor_turns": turns,
            "rational60_free_points_NEW134rod_model": rational,
            "exact_necessary_model_realization_result": exact,
            "NEW_full134rod_stress_kernel_certificate": stress_certificate,
            "NEW_full134rod_stress_exact_identity_controls": stress_identity,
            "NEW_stress_old_diagonal_certificate": old_certificate,
            "NEW_stress_old_diagonal_result": old_result,
            "NEW_stress_correlated_certificate": certificate,
            "NEW_stress_correlated_result": result,
            "known_feasible_tiny_stress_positive_control": tiny_result,
            "numerical_minimax_and_equilibrium_suggestions_NOT_proofs": numerical,
            "numerical_correlated_bound_suggestion_NOT_proof": bound_suggestion,
        })
        print(json.dumps({"checked_v7_leaf": leaf["index"],
                          "exact_below_Rstar_full134rod_RELAXATION_only":
                              exact["exact_below_Rstar_complete134rod_NECESSARY_model_realization"],
                          "fresh_stress_strict_whole_leaf": result is not None and result["arithmetic_strict_target_test_passed"],
                          "verified": False, "new_geometric_payments": 0}), flush=True)
    prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "checked_v7_forest_sha256": digests[args.seed],
        "checked_v7_forest_controls_sha256": digests[args.seed_controls],
        "actual_current_audit_sha256": digests[args.current_audit],
        "actual_latest_candidate_layer_identity_only": layer,
        "correlated_diagnosis_sha256": digests[args.correlated_diagnosis],
        "correlated_actual_independent_controls_sha256": digests[args.correlated_controls],
        "NEW_distinct_full134rod_edges": model["edges"], "results": results,
        "checked_v7_and_NEWEST_running_v8_forests_NONOPEN_proofs_and_supports_UNMODIFIED": True,
        "successful_v7_stress_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction": True,
        "continuous_disk_cover_and_global_optimality_counterexample_NOT_proved": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "independent_exact_realization_and_NEW_stress_arithmetic_controls_still_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (full, prior_producer, prior_producer.correlated, prior_controls)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"full134rod_minimax_relaxation_probe_completed": True,
                      "actual_checked_v7_leaves": len(results),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
