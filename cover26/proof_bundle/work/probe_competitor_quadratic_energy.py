"""Numerical stress-weighted Schur convexity diagnostics, never lower proofs."""

import argparse
from fractions import Fraction as F
import json
from math import pi
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

import probe_free_angle_candidate_rods as joint_module
from probe_retained_joint_force import RetainingJointSolver
from probe_anchor_schur_convexity import hessian_minorant
from n26_sharp_radius_constraints import SCALE
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--only-groups", type=int, nargs="+")
    parser.add_argument("--per-type", type=int, default=1)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.registry)
    radius = F(accepted["radius_upper"])
    domains = {row["group_index"]: row["matrix"] for row in read(args.registry / "DOMAINS.json")}
    results = []
    for row in read(args.registry / "PENDING-TYPES.json"):
        index = row["group_index"]
        if not row["closed_OPEN_boxes"] or (args.only_groups and index not in args.only_groups):
            continue
        boxes = sorted(row["closed_OPEN_boxes"], key=lambda box:
                       sum((F(b) - F(a))**2 for a, b in zip(box["lower"], box["upper"])))
        solver = RetainingJointSolver(row["spec"])
        matrix = domains[index]
        for box in boxes[:args.per_type]:
            captured, original = [], joint_module.minimize

            def capture(*call_args, **kwargs):
                result = original(*call_args, **kwargs)
                captured.append(result)
                return result

            joint_module.minimize = capture
            try:
                value = solver.solve_retained(list(map(F, box["lower"])), list(map(F, box["upper"])), matrix, radius)
            finally:
                joint_module.minimize = original
            optimized = captured[-1]
            b = solver.b
            turns = np.r_[0., value["joint_angles"]]
            anchors = np.c_[np.cos(2 * pi * turns), np.sin(2 * pi * turns)]
            points = np.vstack((anchors, value["joint_center_coordinates"], value["joint_internal_witness_coordinates"]))
            ds = points[solver.E[:, 0]] - points[solver.E[:, 1]]
            lengths = np.linalg.norm(ds, axis=1)
            weights = np.maximum(optimized.multipliers[:len(solver.edges)] /
                                 np.maximum(lengths, 1e-15), 1e-8)
            lap = np.zeros((solver.vertices, solver.vertices))
            for (u, v), weight in zip(solver.edges, weights):
                lap[u, u] += weight
                lap[v, v] += weight
                lap[u, v] -= weight
                lap[v, u] -= weight
            harmonic = -np.linalg.solve(lap[b:, b:], lap[b:, :b])
            schur = lap[:b, :b] + lap[:b, b:] @ harmonic
            coupling = np.maximum(-schur, 0.)
            np.fill_diagonal(coupling, 0.)
            lower, upper = np.r_[0., [float(F(x)) for x in box["lower"]]], np.r_[
                0., [float(F(x)) for x in box["upper"]]]
            eigen = float(np.linalg.eigvalsh(hessian_minorant(coupling, matrix, lower, upper))[0])
            i, j = np.triu_indices(b, 1)
            w, delta = coupling[i, j], 2 * pi * (turns[j] - turns[i])
            energy = 2 * np.dot(w, 1 - np.cos(delta))
            gradient = np.zeros(b)
            np.add.at(gradient, i, -4 * pi * w * np.sin(delta))
            np.add.at(gradient, j, 4 * pi * w * np.sin(delta))
            rows, costs = [], []
            for u in range(b):
                for v in range(b):
                    if u == v:
                        continue
                    coefficients = np.zeros(b - 1)
                    if u:
                        coefficients[u - 1] -= 1
                    if v:
                        coefficients[v - 1] += 1
                    rows.append(coefficients)
                    costs.append(float(F(matrix[u][v], SCALE)))
            lp = linprog(gradient[1:], A_ub=rows, b_ub=costs,
                         bounds=list(zip(lower[1:], upper[1:])), method="highs")
            margin = float(energy + lp.fun - gradient @ turns - float(radius)**2 * sum(weights)) if lp.success else None
            records = {"group_index": index, "index": box["index"],
                       "floating_hessian_minorant_minimum_eigenvalue": eigen,
                       "floating_convex_tangent_energy_margin_if_convexity_were_proved": margin,
                       "proposed_convex_whole_box_energy_payment":
                           bool(eigen > 1e-8 and margin is not None and margin > 1e-10),
                       "floating_weights": weights.tolist(),
                       "floating_stationary_angles": turns[1:].tolist()}
            results.append(records)
            print(json.dumps({key: value for key, value in records.items()
                              if key not in ("floating_weights", "floating_stationary_angles")}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-competitor-quadratic-Schur-energy-diagnostics-v1",
        "verified": False, "registry_acceptance_sha256": sha(args.registry / "VERIFIED.json"),
        "radius_scope": accepted["radius_scope"], "results": results,
        "exact_nonnegative_weights_inverse_LDL_and_linear_duals_still_required": True,
        "floating_eigenvalues_and_tangent_LP_numbers_are_not_proofs": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
