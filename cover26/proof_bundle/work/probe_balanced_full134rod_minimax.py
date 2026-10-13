"""Distinct unscaled primal minimax replay; old numerical reports are intact."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import lsq_linear, minimize

from audit_prefix_partition import linux
import probe_full134rod_minimax_relaxation as old
import test_full134rod_minimax_relaxation as old_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-balanced-full134rod-fixed-anchor-minimax-diagnosis-v1"
full = old.full


def balanced_suggestion(model, kernel, turns, iterations):
    anchors = np.array([[np.cos(2*np.pi*float(turn)), np.sin(2*np.pi*float(turn))]
                        for turn in [F(0), *turns]])
    harmonic = np.array([[float(F(value, kernel["inverse_denominator"])) for value in row]
                         for row in kernel["harmonic"]])
    initial_free = harmonic@anchors
    edges = np.array(model["edges"])
    left, right = edges[:, 0], edges[:, 1]

    def positions(x):
        return np.vstack((anchors, x[:120].reshape(60, 2)))

    def squared_rods(x):
        points = positions(x)
        differences = points[left]-points[right]
        return np.einsum("ij,ij->i", differences, differences)

    def constraint(x):
        free = x[:120].reshape(60, 2)
        return np.r_[x[-1]-squared_rods(x), 1-np.einsum("ij,ij->i", free, free)]

    def jacobian(x):
        points = positions(x)
        jac = np.zeros((194, 121))
        for index, (u, v) in enumerate(model["edges"]):
            difference = points[u]-points[v]
            if u >= 16:
                jac[index, 2*(u-16):2*(u-16)+2] = -2*difference
            if v >= 16:
                jac[index, 2*(v-16):2*(v-16)+2] += 2*difference
            jac[index, -1] = 1
        for index, point in enumerate(points[16:]):
            jac[134+index, 2*index:2*index+2] = -2*point
        return jac

    initial = np.r_[initial_free.ravel(), 1.]
    initial[-1] = float(max(squared_rods(initial)))+1e-5
    derivative = np.r_[np.zeros(120), 1.]
    # Numerical finite-difference control on actual initial constraints, not
    # a proof of the minimizer or a distance certificate.
    h, maximum_error = 1e-6, 0.
    actual_jacobian = jacobian(initial)
    for column in (0, 17, 63, 119, 120):
        plus, minus = initial.copy(), initial.copy()
        plus[column] += h
        minus[column] -= h
        finite = (constraint(plus)-constraint(minus))/(2*h)
        maximum_error = max(maximum_error, float(np.max(np.abs(finite-actual_jacobian[:, column]))))
    if maximum_error > 1e-6:
        raise ValueError("actual unscaled minimax numerical constraint derivative control failed")
    optimized = minimize(
        lambda x: float(x[-1]), initial, jac=lambda x: derivative, method="SLSQP",
        bounds=[(-1., 1.)]*120+[(0., 1.)],
        constraints={"type": "ineq", "fun": constraint, "jac": jacobian},
        options={"ftol": 1e-13, "maxiter": iterations, "disp": False})
    if not np.all(np.isfinite(optimized.x)):
        raise ValueError("balanced full134rod minimax returned nonfinite suggestions")
    points, squared = positions(optimized.x), squared_rods(optimized.x)
    equilibrium = -jacobian(optimized.x)[:134, :120].T
    active = max(squared)-squared <= 1e-7
    stress = lsq_linear(
        np.vstack((equilibrium, np.ones(134))), np.r_[np.zeros(120), 1.],
        bounds=(np.full(134, 1e-12), np.where(active, 1., 1e-8)),
        method="trf", tol=1e-13, max_iter=iterations)
    weights = np.maximum(stress.x, 1e-12)
    weights /= weights.sum()
    return points[16:], weights, {
        "numerical_objective_scale": 1,
        "numerical_actual_finite_difference_Jacobian_error_NOT_proof": maximum_error,
        "numerical_convex_minimax_success_NOT_proof": bool(optimized.success),
        "numerical_convex_minimax_message": str(optimized.message),
        "numerical_convex_minimax_iterations": int(optimized.nit),
        "numerical_max_squared_rod_NOT_a_radius_certificate": float(max(squared)),
        "numerical_primal_constraint_minimum_NOT_proof": float(min(constraint(optimized.x))),
        "numerical_active_rod_count_DATA": int(active.sum()),
        "numerical_stress_fit_success_NOT_proof": bool(stress.success),
        "numerical_free_equilibrium_residual_NOT_proof": float(np.max(np.abs(equilibrium@weights))),
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "correlated-diagnosis", "correlated-controls",
                 "old-minimax-diagnosis", "old-minimax-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=600)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if not 1 <= args.iterations <= 1000:
        raise ValueError("invalid balanced minimax limits")
    original, model, seed, ancestor, prior, row, arcs, digests, layer = old.prior_producer.input_gate(args)
    previous = binding.read(args.old_minimax_diagnosis)
    controls = binding.read(args.old_minimax_controls)
    for path in (args.old_minimax_diagnosis, args.old_minimax_controls,
                 args.correlated_diagnosis, args.correlated_controls):
        digests[path] = binding.sha(path)
    if (previous["schema"] != old.SCHEMA
            or previous["executed_probe_sha256"] != binding.sha(old.__file__)
            or previous["checked_v7_forest_sha256"] != digests[args.seed]
            or previous["source_file_sha256"] != seed["source_file_sha256"]
            or controls["schema"] != old_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(old_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.old_minimax_diagnosis]
            or controls["tested_minimax_probe_sha256"] != binding.sha(old.__file__)
            or len(controls["actual_point_dimension_radius_scope_and_fresh_stress_rejection_controls_passed"]) != 16
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0):
        raise ValueError("balanced replay changed actual old minimax data or independent controls")
    actual = {item["actual_newest_OPEN_leaf"]["index"]: item["actual_newest_OPEN_leaf"]
              for item in prior["results"]}
    radius_lower = binding.read(args.current_audit)["r_strict_interval"][0]
    root_box = old.prior_producer.previous.producer.latest_controls.producer.BASE.tighten(
        original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    results = []
    for item in previous["results"]:
        leaf, turns = item["actual_checked_v7_OPEN_leaf"], item["actual_fixed_feasible_anchor_turns"]
        if leaf != actual[leaf["index"]]:
            raise ValueError("balanced replay changed the actual checked v7 closed leaf")
        kernel, _ = old.prior_producer.previous.arithmetic.kernel_controls(
            model, item["NEW_full134rod_stress_kernel_certificate"])
        points, weights, numerical = balanced_suggestion(model, kernel, list(map(F, turns)), args.iterations)
        rational = [[str(F(round(float(value)*10**16), 10**16)) for value in point] for point in points]
        exact = old.exact_relaxation(model, original["matrix"], leaf, turns, rational, radius_lower, arcs)
        stress_certificate, stress_kernel = old.prior_producer.previous.producer.old_probe.exact_kernel(model, weights)
        identity = full.native_graph.identity_control(stress_kernel)
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        diagonal, diagonal_result = old.prior_producer.previous.producer.old_probe.suggest_bound(
            original, stress_kernel, box, list(map(F, turns)), tight, arcs, 16)
        certificate, result, bound_suggestion = None, None, None
        if diagonal is not None:
            certificate, result, bound_suggestion = old.prior_producer.suggest(
                stress_kernel, original, leaf, diagonal, arcs)
        tiny = original["cap"]["known_candidate_tiny_angle_cells"]
        tiny_result = full.direct.bound(
            [a for a, _ in tiny], [b for _, b in tiny], stress_kernel, F(original["radius"])**2, arcs)
        if tiny_result["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("balanced minimax stress excludes known feasible tiny candidate")
        results.append({
            "actual_checked_v7_OPEN_leaf": leaf, "actual_fixed_feasible_anchor_turns": turns,
            "rational60_free_points_NEW134rod_model": rational,
            "exact_necessary_model_realization_result": exact,
            "NEW_full134rod_stress_kernel_certificate": stress_certificate,
            "NEW_full134rod_stress_exact_identity_controls": identity,
            "NEW_stress_old_diagonal_certificate": diagonal, "NEW_stress_old_diagonal_result": diagonal_result,
            "NEW_stress_correlated_certificate": certificate, "NEW_stress_correlated_result": result,
            "known_feasible_tiny_stress_positive_control": tiny_result,
            "numerical_minimax_and_equilibrium_suggestions_NOT_proofs": numerical,
            "numerical_correlated_bound_suggestion_NOT_proof": bound_suggestion,
        })
        print(json.dumps({"checked_v7_leaf": leaf["index"],
                          "exact_below_Rstar_full134rod_RELAXATION_only":
                              exact["exact_below_Rstar_complete134rod_NECESSARY_model_realization"],
                          "fresh_balanced_stress_strict_whole_leaf":
                              result is not None and result["arithmetic_strict_target_test_passed"],
                          "verified": False, "new_geometric_payments": 0}), flush=True)
    old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": row["index"],
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "checked_v7_forest_sha256": digests[args.seed], "checked_v7_forest_controls_sha256": digests[args.seed_controls],
        "actual_current_audit_sha256": digests[args.current_audit],
        "actual_latest_candidate_layer_identity_only": layer,
        "old_minimax_diagnosis_sha256": digests[args.old_minimax_diagnosis],
        "old_minimax_actual_independent_controls_sha256": digests[args.old_minimax_controls],
        "NEW_distinct_full134rod_edges": model["edges"], "results": results,
        "old_numerical_data_reports_and_NEWEST_running_FORESTS_UNMODIFIED": True,
        "successful_v7_stress_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction": True,
        "continuous_disk_cover_and_global_optimality_counterexample_NOT_proved": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "independent_balanced_primal_and_fresh_stress_controls_still_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (old, old_controls, full, old.prior_producer, old.prior_producer.correlated)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"balanced_full134rod_minimax_probe_completed": True,
                      "actual_checked_v7_leaves": len(results),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
