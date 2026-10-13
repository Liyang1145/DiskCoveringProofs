"""Test actual nonredundant B17 prefixes, preserving all frozen source inputs."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from sympy import Matrix

from audit_b17_short_gap_actual_domains import closed
from audit_prefix_origin import OriginReference
import n26_b17_radial_origin_energy as radial
import n26_force as force
import verify_conditional_force_stage as binding


def branch_matrix(matrix, owner):
    result = [row[:] for row in matrix]
    if owner:
        result[owner-1][owner] = min(result[owner-1][owner], int(radial.ALPHA*force.D))
    else:
        result[16][0] = min(result[16][0], int((radial.ALPHA-1)*force.D))
    return closed(result)


def suggest_weights(spec, owner, turns, iterations):
    vertices, edges = radial.partial.graph(spec)
    anchors = np.array([[np.cos(2*np.pi*float(t)), np.sin(2*np.pi*float(t))] for t in turns])
    count = len(edges)

    def value(variables):
        weights, mu = variables[:-1], variables[-1]
        matrix = np.zeros((vertices, vertices))
        for (u, v), w in zip(edges, weights):
            matrix[u, u] += w
            matrix[v, v] += w
            matrix[u, v] -= w
            matrix[v, u] -= w
        matrix[17+owner, 17+owner] += mu
        free = np.linalg.solve(matrix[17:, 17:], -matrix[17:, :17]@anchors)
        points = np.vstack((anchors, free))
        squared = np.array([np.dot(points[u]-points[v], points[u]-points[v]) for u, v in edges])
        radial_derivative = np.dot(free[owner], free[owner])-float(radial.KAPPA**2)
        energy = float(np.dot(weights, squared)+mu*radial_derivative)
        return -energy, -np.r_[squared, radial_derivative]

    initial = np.r_[np.full(count, 1/count), .01]
    optimized = minimize(
        value, initial, jac=True, method="SLSQP",
        bounds=[(1e-8, 1.)]*count+[(0., 10.)],
        constraints={"type": "eq", "fun": lambda x: x[:-1].sum()-1,
                     "jac": lambda x: np.r_[np.ones(count), 0.]},
        options={"maxiter": iterations, "ftol": 1e-12, "disp": False})
    weights = np.maximum(optimized.x[:-1], 1e-8)
    weights /= weights.sum()
    mu = max(0., float(optimized.x[-1]))
    return weights, mu, {
        "numerical_weight_search_success_NOT_proof": bool(optimized.success),
        "numerical_iterations": int(optimized.nit),
        "numerical_fixed_anchor_energy_NOT_proof": -float(optimized.fun),
    }


def exact_kernel(spec, owner, weights, mu):
    scale = 10**16
    integers = [max(1, round(float(w)*scale)) for w in weights]
    origin = max(0, round(mu*scale))
    _, _, matrix = radial.matrix_from_weights(spec, integers, origin, owner)
    inverse, den = Matrix([row[17:] for row in matrix[17:]]).to_DM().inv_den()
    inverse, den = [[int(v) for v in row] for row in inverse.to_Matrix().tolist()], int(den)
    if den < 0:
        inverse, den = [[-v for v in row] for row in inverse], -den
    certificate = {
        "schema": radial.SCHEMA, "spec": spec, "owner": owner, "kappa": str(radial.KAPPA),
        "weight_scale": scale, "weight_numerators": integers,
        "origin_weight_numerator": origin, "inverse_denominator": str(den),
        "inverse_numerators": [[str(v) for v in row] for row in inverse],
    }
    return certificate, radial.kernel_gate(spec, certificate)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--states", type=int, default=1)
    parser.add_argument("--iterations", type=int, default=120)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.states <= 8 or not 1 <= args.iterations <= 500:
        raise ValueError("preserve old results and use a bounded actual-state experiment")
    stage = Path("outputs/n26-conditional-force-stage-v35-sparse-v1")
    source = stage/"FRONTIER.json"
    accepted = binding.read(stage/"VERIFIED.json")
    if binding.sha(source) != accepted["files"]["FRONTIER.json"]:
        raise ValueError("actual accepted B17 source changed")
    audit_path = Path("outputs/n26-b17-short-gap-actual-domain-audit-v1.json")
    arithmetic_path = Path("outputs/n26-b17-nine-disk-core-short-gap-arithmetic-v1.json")
    proof_path = Path("work/n26-b17-radial-origin-energy-proof.md")
    current_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    paths = [source, stage/"VERIFIED.json", audit_path, arithmetic_path, proof_path, current_path,
             Path(__file__), Path(radial.__file__), Path(force.__file__),
             Path(radial.partial.__file__), Path("work/n26_pairwise_affine_energy.py"),
             Path("work/audit_b17_short_gap_actual_domains.py")]
    digests = {str(path): binding.sha(path) for path in paths}
    audit, arithmetic = binding.read(audit_path), binding.read(arithmetic_path)
    if (audit["whole_actual_states_excluded_by_gap_bounds"] != 0
            or arithmetic["necessary_deep_boundary_center_norm_upper"] != str(radial.KAPPA)
            or F(arithmetic["necessary_at_least_one_cyclic_ownership_gap_STRICTLY_below_turns"]) != radial.ALPHA):
        raise ValueError("actual new radial theorem/domain audit changed")
    wanted = {tuple(row["actual_source_prefix"]) for row in audit["results"]
              if row["exact_new_constraint_removes_an_old_angular_point"]}
    rows = [row for row in binding.read(source)["pending_states"]
            if row["B"] == 17 and tuple(row["prefix"]) in wanted][-args.states:]
    reference = OriginReference(26, 17, "dfs", caps=force.CAPS, scale=force.D)
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    arcs = force.load_trig(resource)[0]
    radius = F(binding.read(current_path)["r_strict_interval"][1])
    results = []
    for row in rows:
        prefix = tuple(row["prefix"])
        state = reference.resolve(prefix)
        if {"B": 17, **reference.entry(prefix, state, reference.children(state))} != row:
            raise ValueError("actual B17 source state did not reconstruct")
        spec = {"N": 26, "B": 17, "next": row["next"], "faces": row["faces"]}
        matrix, branches = force.angular_domain(spec), []
        for owner in range(17):
            domain = branch_matrix(matrix, owner)
            if domain is None:
                branches.append({"owner": owner, "branch_angular_domain_empty": True})
                continue
            turns = [F(domain[0][j]-domain[j][0], 2*force.D) for j in range(17)]
            if turns[0] != 0 or any(turns[j]-turns[i] > F(domain[i][j], force.D)
                                    for i in range(17) for j in range(17)):
                raise AssertionError("closed shortest-path midpoint is not exactly feasible")
            weights, mu, numerical = suggest_weights(spec, owner, turns, args.iterations)
            certificate, kernel = exact_kernel(spec, owner, weights, mu)
            identity = radial.identity_control(kernel)
            point = radial.point_interval(kernel, turns, arcs)
            affine_certificate, bound, lp = radial.suggest(radial.prepare(kernel, domain, arcs), domain, radius)
            # Same ORIGINAL rod weights, fresh ZERO-multiplier inverse: not a
            # mislabeled inherited kernel and not a mu-in-the-radius-cap comparison.
            baseline_certificate, baseline = exact_kernel(spec, owner, weights, 0.)
            baseline_point = radial.point_interval(baseline, turns, arcs)
            radial.identity_control(baseline)
            _, baseline_bound, _ = radial.suggest(radial.prepare(baseline, domain, arcs), domain, radius)
            branch = {
                "owner": owner, "branch_angular_domain_empty": False,
                "exact_feasible_anchor_turns": list(map(str, turns)),
                "radial_kernel_certificate": certificate, "identity_control": identity,
                "exact_fixed_point_lower": str(point[0]),
                "exact_fixed_point_margin_above_Rstar_upper_squared": str(point[0]-radius**2),
                "baseline_zero_origin_kernel_certificate": baseline_certificate,
                "baseline_exact_fixed_point_lower": str(baseline_point[0]),
                "exact_fixed_point_radial_gain_over_identical_rod_weights": str(point[0]-baseline_point[1]),
                "whole_branch_affine_certificate": affine_certificate,
                "whole_branch_exact_result": bound,
                "baseline_whole_branch_exact_result": baseline_bound,
                "numerical_weight_suggestion_NOT_proof": numerical,
                "numerical_affine_suggestion_NOT_proof": lp,
            }
            branches.append(branch)
            print(json.dumps({
                "actual_prefix": row["prefix"], "owner": owner,
                "exact_origin_multiplier_positive": kernel["origin_weight"] > 0,
                "exact_point_radial_gain_positive": point[0] > baseline_point[1],
                "strict_entire_radial_branch": bound is not None and bound["arithmetic_strict_entire_radial_branch"],
                "new_geometric_payments": 0,
            }), flush=True)
        strict = sum(not b["branch_angular_domain_empty"] and b["whole_branch_exact_result"] is not None
                     and b["whole_branch_exact_result"]["arithmetic_strict_entire_radial_branch"] for b in branches)
        empty = sum(b["branch_angular_domain_empty"] for b in branches)
        results.append({
            "actual_source_state": row, "actual_partial_spec": spec, "branches": branches,
            "all17branches_accounted": len(branches) == 17,
            "empty_branches": empty, "strict_entire_radial_branches": strict,
            "arithmetic_all17branches_strict_or_empty": strict+empty == 17,
        })
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("B17 source/input/module changed during mathematical experiment")
    report = {
        "schema": "N26-B17-actual-inward-owner-ground-energy-pilot-v1",
        "verified": False, "results": results, "input_sha256": digests,
        "actual_states_tested": len(results),
        "actual_complete17branch_covers_arithmetically_excluded": sum(
            row["arithmetic_all17branches_strict_or_empty"] for row in results),
        "original_source_forests_histories_and_ledgers_UNMODIFIED": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "actual_states_tested", "actual_complete17branch_covers_arithmetically_excluded",
        "new_geometric_payments")}), flush=True)


if __name__ == "__main__":
    main()
