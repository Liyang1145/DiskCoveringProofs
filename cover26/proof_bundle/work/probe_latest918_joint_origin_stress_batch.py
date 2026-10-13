"""Fresh joint primal/stress suggestions on WHOLE actual latest918 OPEN leaves.

No old executor or proof is modified. Numerical minimization suggests a
reference and134 positive rod weights; exact whole-domain energy decides.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import lsq_linear, minimize

from audit_prefix_partition import linux
import n26_latest918_joint_stress_source as source
import n26_origin_branch_correlated_energy as energy
import probe_joint_fresh_origin25_stress_successor as fresh
import probe_joint_remaining_origin25_primal as angle_recovery
import probe_remaining_origin25_primal_relaxation as fixed_primal
import probe_latest_root25_two_origin_whole_leaves as ranking
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest918-joint-origin-fresh-stress-batch-v1"
PROOF = Path("work/n26-latest918-joint-origin-stress-batch-proof.md")


def joint_suggestion(original, model, base, leaf, owner, iterations):
    lo = np.array(list(map(float, map(F, leaf["lower"]))))
    hi = np.array(list(map(float, map(F, leaf["upper"]))))
    widths = hi-lo
    turns = [(F(a)+F(b))/2 for a, b in zip(leaf["lower"], leaf["upper"])]
    energy.scalar.full.hull.quadratic.reference_gate(turns, leaf["lower"], leaf["upper"], original["matrix"])
    initial_free, fixed_choices = fixed_primal.numerical_minimax(model, base, turns, owner, iterations)
    rows, rhs = [], []
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            vector = np.zeros(15)
            if i:
                vector[i-1] += widths[i-1]
            if j:
                vector[j-1] -= widths[j-1]
            fixed = (lo[i-1] if i else 0)-(lo[j-1] if j else 0)
            constant = float(F(original["matrix"][i][j], 10**40))+fixed
            scale = max(float(max(abs(vector))), abs(constant), 1e-10)
            rows.append(vector/scale)
            rhs.append(constant/scale)
    rows, rhs = np.array(rows), np.array(rhs)
    edges = np.array(model["edges"])

    def positions(x):
        theta = np.r_[0., lo+widths*x[120:135]]
        anchors = np.column_stack((np.cos(2*np.pi*theta), np.sin(2*np.pi*theta)))
        return np.vstack((anchors, x[:120].reshape(60, 2))), anchors

    def constraints(x):
        points, _ = positions(x)
        deltas, free_points = points[edges[:, 0]]-points[edges[:, 1]], points[16:]
        return np.r_[x[-1]-np.einsum("ij,ij->i", deltas, deltas),
                     1-np.einsum("ij,ij->i", free_points, free_points),
                     x[-1]-free_points[owner]@free_points[owner], rhs+rows@x[120:135]]

    def jacobian(x):
        points, anchors = positions(x)
        derivatives = 2*np.pi*np.column_stack((-anchors[1:, 1], anchors[1:, 0]))*widths[:, None]
        jac = np.zeros((435, 136))
        for index, (u, v) in enumerate(model["edges"]):
            delta = points[u]-points[v]
            if u >= 16:
                jac[index, 2*(u-16):2*(u-16)+2] -= 2*delta
            elif u:
                jac[index, 120+u-1] -= 2*delta@derivatives[u-1]
            if v >= 16:
                jac[index, 2*(v-16):2*(v-16)+2] += 2*delta
            elif v:
                jac[index, 120+v-1] += 2*delta@derivatives[v-1]
            jac[index, -1] = 1
        for index, point in enumerate(points[16:]):
            jac[134+index, 2*index:2*index+2] = -2*point
        jac[194, 2*owner:2*owner+2] = -2*points[16+owner]
        jac[194, -1] = 1
        jac[195:, 120:135] = rows
        return jac

    initial = np.r_[initial_free.ravel(), np.full(15, .5), 1.]
    initial[-1] = 1-min(0., float(min(constraints(initial))))+1e-5
    h, error = 1e-6, 0.
    numerical_jacobian = jacobian(initial)
    for column in (0, 2*owner, 2*owner+1, 119, 120, 126, 130, 134, 135):
        left, right = initial.copy(), initial.copy()
        left[column] += h
        right[column] -= h
        finite = (constraints(left)-constraints(right))/(2*h)
        error = max(error, float(max(abs(finite-numerical_jacobian[:, column]))))
    if error > 1e-6:
        raise ValueError("fresh actual joint-origin numerical Jacobian differs")
    optimized = minimize(
        lambda x: float(x[-1]), initial, jac=lambda x: np.r_[np.zeros(135), 1.],
        method="SLSQP", bounds=[(-1., 1.)]*120+[(0., 0. if width == 0 else 1.) for width in widths]+[(0., 2.)],
        constraints={"type": "ineq", "fun": constraints, "jac": jacobian},
        options={"ftol": 1e-13, "maxiter": iterations, "disp": False})
    if not np.all(np.isfinite(optimized.x)):
        raise ValueError("fresh joint-origin numerical suggestions nonfinite")
    exact_turns, recovery = angle_recovery.exact_turns(original, leaf, lo+widths*optimized.x[120:135])
    rational_free = [
        [str(F(round(float(value)*10**17), 10**17)) for value in point]
        for point in optimized.x[:120].reshape(60, 2)
    ]
    return exact_turns, rational_free, {
        "fixed_anchor_numerical_initialization_NOT_proof": fixed_choices,
        "numerical_joint_success_NOT_proof": bool(optimized.success),
        "numerical_joint_message": str(optimized.message), "numerical_joint_iterations": int(optimized.nit),
        "numerical_joint_squared_radius_NOT_proof": float(optimized.x[-1]),
        "numerical_joint_minimum_constraint_NOT_proof": float(min(constraints(optimized.x))),
        "numerical_Jacobian_finite_difference_error_NOT_proof": error,
        "all15_anchors_and60free_positions_varied_WITHOUT_symmetry": True,
        "exact_reference_angle_recovery": recovery,
    }


def stress_suggestion(model, turns, rational_free, owner):
    anchors = np.array([[np.cos(2*np.pi*float(t)), np.sin(2*np.pi*float(t))] for t in [F(0), *turns]])
    free_points = np.array([[float(F(value)) for value in point] for point in rational_free])
    positions, matrix, squared = np.vstack((anchors, free_points)), np.zeros((120, 135)), []
    for index, (u, v) in enumerate(model["edges"]):
        delta = positions[u]-positions[v]
        squared.append(float(delta@delta))
        if u >= 16:
            matrix[2*(u-16):2*(u-16)+2, index] += 2*delta
        if v >= 16:
            matrix[2*(v-16):2*(v-16)+2, index] -= 2*delta
    squared.append(float(free_points[owner]@free_points[owner]))
    matrix[2*owner:2*owner+2, 134] = 2*free_points[owner]
    squared = np.array(squared)
    active = max(squared)-squared <= 1e-7
    optimized = lsq_linear(
        np.vstack((matrix, np.ones(135))), np.r_[np.zeros(120), 1.],
        bounds=(np.full(135, 1e-13), np.where(active, 1., 1e-8)),
        method="trf", tol=1e-13, max_iter=500)
    weights = np.maximum(optimized.x, 1e-13)
    weights /= weights.sum()
    return weights[:134], weights[134], {
        "numerical_stress_fit_success_NOT_proof": bool(optimized.success),
        "numerical_active_physical_and_origin_constraints": int(active.sum()),
        "numerical_free_equilibrium_residual_NOT_proof": float(max(abs(matrix@weights))),
        "origin_multiplier_NOT_a135th_physical_rod": True,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=8)
    parser.add_argument("--parts", type=int, default=16)
    parser.add_argument("--iterations", type=int, default=700)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 64 or not 1 <= args.parts <= 64 or not 1 <= args.iterations <= 1500:
        raise ValueError("fresh bounded latest918 joint-stress batch required")
    original, model, bases, seed, controls, row, pending, arcs, inventory = source.inputs()
    ranks = ranking.rank(original, bases, pending)
    by_index = {leaf["index"]: leaf for leaf in pending}
    results, strict = [], []
    print(json.dumps({
        "actual_paired918_source_and582_prior_strict_rows_reconstructed": True,
        "actual_fresh_joint_stress_whole_leaf_limit": args.limit,
        "numerical_ranking_NOT_lower_bound_top_indices": [item["actual_prior_OPEN_leaf_index"] for item in ranks[:args.limit]],
    }), flush=True)
    for number, rank in enumerate(ranks[:args.limit], 1):
        leaf = by_index[rank["actual_prior_OPEN_leaf_index"]]
        trials = []
        for owner in (16, 25):
            support = rank["branch_parameter_suggestions"][owner][0]["full_support_index"]
            turns, free_points, primal = joint_suggestion(original, model, bases[support], leaf, owner, args.iterations)
            weights, mu, stress = stress_suggestion(model, turns, free_points, owner)
            base_certificate, base = fresh.exact_base(model, weights)
            multiplier = F(max(0, round(float(mu)*10**30)), 10**30)
            kernel = energy.origin.kernel_gate(base, original["data"][3], owner, multiplier)
            certificate, result, choices = energy.suggest(
                kernel, original["matrix"], list(map(F, leaf["lower"])), list(map(F, leaf["upper"])),
                turns, original["radius"], arcs, args.parts)
            proved = result is not None and result["arithmetic_strict_entire_origin_branch"] is True
            trials.append({
                "origin_center_label": owner,
                "fresh_positive134rod_kernel_certificate": base_certificate,
                "fresh_origin_multiplier": str(multiplier),
                "joint_reference_turns": list(map(str, turns)), "joint_rational60_free_points": free_points,
                "whole_origin_branch_certificate": certificate, "whole_origin_branch_arithmetic_result": result,
                "fresh_exact_whole_origin_branch_strict": proved,
                "numerical_joint_primal_NOT_proof": primal, "numerical_stress_fit_NOT_proof": stress,
                "numerical_curvature_suggestion_NOT_proof": choices,
            })
            print(json.dumps({
                "actual_latest918_whole_leaf": leaf["index"], "origin_owner": owner,
                "fresh_exact_whole_origin_branch_strict": proved,
                "exact_energy_margin_display": float(F(result["strict_energy_margin"])) if result else None,
                "both_origin_owners_required": True, "formal_geometric_payments": 0,
            }), flush=True)
        whole = all(trial["fresh_exact_whole_origin_branch_strict"] for trial in trials)
        results.append({
            "actual_latest918_whole_OPEN_leaf": leaf, "actual_origin_branch_trials": trials,
            "BOTH_whole_origin_branches_strict": whole,
        })
        if whole:
            strict.append(leaf["index"])
        print(json.dumps({
            "completed_fresh_joint_whole_leaf_attempts": number, "of": args.limit,
            "fresh_BOTH_branch_whole_leaf_exclusions": len(strict),
            "current918_not_yet_changed_pending_independent_join": True,
        }), flush=True)
    for module in (source, energy, fresh, angle_recovery, fixed_primal, ranking):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(PROOF): binding.sha(PROOF), linux(__file__): binding.sha(__file__)})
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("latest918 joint-stress prerequisite changed during exact calculation")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "actual_paired918_diagnosis_sha256": source.SEED_SHA,
        "actual_paired918_controls_sha256": source.CONTROL_SHA,
        "actual_joint_stress_whole_leaf_trials": results,
        "actual_new_strict_whole_leaf_indices": sorted(strict),
        "prospective_arithmetic_remaining_OPEN_after_independent_join": 918-len(strict),
        "latest918_global_nodes_and582_strict_ledger_rows_UNMODIFIED": True,
        "all66_prior_whole_exclusions_and_complete2641_branch_forest_retained": True,
        "fresh_positive_kernels_and_all_whole_closed_origin_bounds_freshly_computed": True,
        "numeric_minima_AND_stress_residuals_NOT_infeasibility_proofs": True,
        "new_independent_exact_kernel_arithmetic_and_source_retention_STILL_required": True,
        "entire_latest_source_model_geometry_current_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_producer_sha256": binding.sha(__file__),
    }
    source.target_gate(report, seed, pending)
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "latest918_fresh_joint_stress_primary_completed_NOT_admission": True,
        "new_BOTH_branch_whole_leaf_indices": sorted(strict),
        "prospective_remaining_OPEN_PENDING_independent_composition": 918-len(strict),
    }), flush=True)


if __name__ == "__main__":
    main()
