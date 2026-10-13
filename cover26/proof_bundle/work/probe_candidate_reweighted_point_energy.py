"""Unadmitted alternative positive support on the SAME original 92 rods.

Numerical weights are only suggestions. A fresh exact integer inverse and
outward trigonometry determine whether the fixed-energy-limit point can be
excluded by a different valid necessary rod-energy support. No whole root,
free-vertex realization, continuous disk cover, or current admission is claimed.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
from sympy import Matrix

from audit_prefix_partition import linux
import n26_dirichlet_energy as dirichlet
import n26_quadratic_energy_minorant as energy
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def float_energy(edges, weights, anchors):
    laplacian = np.zeros((62, 62))
    for (a, b), weight in zip(edges, weights):
        laplacian[a, a] += weight
        laplacian[b, b] += weight
        laplacian[a, b] -= weight
        laplacian[b, a] -= weight
    free = np.linalg.solve(laplacian[16:, 16:], -laplacian[16:, :16] @ anchors)
    vertices = np.vstack((anchors, free))
    squared = np.array([np.dot(vertices[a] - vertices[b], vertices[a] - vertices[b])
                        for a, b in edges])
    return float(np.dot(weights, squared)), squared


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "point-diagnosis", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=100)
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
        raise ValueError("reweighted diagnosis changed the fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, old_kernel = model["original"], model["original_kernel"]
    accepted = binding.read(args.source / "VERIFIED.json")
    source_digest = binding.sha(args.source / "PENDING-ANGLES.json")
    if source_digest != accepted["files"]["PENDING-ANGLES.json"]:
        raise ValueError("reweighted diagnosis changed actual source root DATA")
    point_digest = binding.sha(args.point_diagnosis)
    point_diagnosis = binding.read(args.point_diagnosis)
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == point_diagnosis["source_OPEN_index"])
    if (point_diagnosis["verified"] is not False
            or point_diagnosis["new_geometric_payments"] != 0
            or point_diagnosis["actual_source_closed_box"] != row
            or point_diagnosis["this_is_NOT_an_actual_rod_realization_or_continuous_disk_cover"] is not True):
        raise ValueError("reweighted point diagnosis changed ownership or claimed a covering construction")
    point = energy.reference_gate(
        point_diagnosis["exact_point_turns"], row["sharp_lower"], row["sharp_upper"],
        original["matrix"])[0]
    edges = old_kernel["edges"]
    if edges != original["reference"]["edges"] or len(edges) != 92:
        raise ValueError("reweighted diagnosis changed original 92-rod geometry")
    anchors = np.array([[np.cos(2*np.pi*float(turn)), np.sin(2*np.pi*float(turn))]
                        for turn in point])
    start = np.array(old_kernel["weights"], dtype=float)
    start /= start.sum()
    base, base_squared = float_energy(edges, start, anchors)

    def objective(log_shift):
        shifted = start * np.exp(log_shift)
        shifted /= shifted.sum()
        value, squared = float_energy(edges, shifted, anchors)
        return -(value - base)*10**8, -shifted*(squared - value)*10**8

    numerical = minimize(
        objective, np.zeros(92), jac=True, method="L-BFGS-B",
        bounds=[(-0.5, 0.5)]*92,
        options={"maxiter": args.iterations, "ftol": 1e-15, "gtol": 1e-9, "maxls": 40})
    shifted = start * np.exp(numerical.x)
    shifted /= shifted.sum()
    suggested_energy, suggested_squared = float_energy(edges, shifted, anchors)
    scale = 10**30
    weights = [max(1, round(float(value)*scale)) for value in shifted]
    reference = deepcopy(original["reference"])
    reference.update(rational_scale=str(scale), weight_numerators=list(map(str, weights)))
    reference["alternative_weights_are_DIAGNOSTIC_not_original_accepted_support"] = True
    laplacian = dirichlet.laplacian(edges, weights)
    print(json.dumps({
        "fresh_alternative_exact_ground_inverse_started": True,
        "same_original_rods": len(edges),
        "floating_support_improvement_NOT_proof": suggested_energy - base,
        "verified": False, "new_geometric_payments": 0}), flush=True)
    inverse, denominator = Matrix([row[16:] for row in laplacian[16:]]).to_DM().inv_den()
    numerator = [[int(value) for value in row] for row in inverse.to_Matrix().tolist()]
    denominator = int(denominator)
    if denominator < 0:
        numerator = [[-value for value in row] for row in numerator]
        denominator = -denominator
    certificate = {
        "schema": "N26-exact-integer-ground-Dirichlet-inverse-v1", "anchor_vertices": 16,
        "inverse_denominator": str(denominator),
        "inverse_numerators": [[str(value) for value in row] for row in numerator],
    }
    fresh = dirichlet.kernel_gate(reference, certificate)
    kernel = {**fresh, "B": 16, "vertices": 62, "edges": edges, "pairs": fresh["pair_weights"],
              "alternative_positive_support_of_original_92_rods_NOT_original_fixed_weights": True}
    arcs = binding.force.load_trig(args.resource)[0]
    lower, _ = energy.point_energy_gradient(kernel, point, arcs)
    upper_num = sum(2*weight*(arcs.SCALE-arcs.sincos_turn(point[j]-point[i])[0][0])
                    for i, j, weight in kernel["pairs"])
    upper = F(upper_num, kernel["energy_denominator"]*arcs.SCALE)
    cap = F(original["radius"])**2 * F(sum(weights), scale)
    if lower > upper:
        raise AssertionError("alternative point-energy interval is reversed")
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_bound = dirichlet.bound(
        [a for a, _ in tiny], [b for _, b in tiny], kernel, F(original["radius"])**2, arcs)
    if tiny_bound["radius_conditional_whole_angle_box_excluded"]:
        raise AssertionError("alternative positive support excludes the known feasible tiny candidate")
    if (binding.sha(args.source / "PENDING-ANGLES.json") != source_digest
            or binding.sha(args.point_diagnosis) != point_digest):
        raise ValueError("actual source DATA or fixed-energy-limit point changed during diagnosis")
    report = {
        "schema": "N26-unaccepted-alternative-original-92-rod-point-energy-diagnosis-v1",
        "verified": False, "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_pending_angles_sha256": source_digest,
        "original_fixed_energy_limit_diagnosis_sha256": point_digest,
        "exact_point_turns": list(map(str, point[1:])),
        "same_original_92_rod_edges_preserved": True,
        "positive_weight_support_is_NEW_NOT_the_original_fixed_kernel": True,
        "alternative_reference_DATA": reference, "alternative_exact_inverse_certificate": certificate,
        "fresh_integer_ground_inverse_harmonic_and_Schur_identities_checked": True,
        "alternative_point_energy_lower": str(lower), "alternative_point_energy_upper": str(upper),
        "alternative_same_root_energy_upper": str(cap),
        "alternative_point_energy_strict_margin": str(lower-cap),
        "alternative_support_arithmetically_excludes_only_this_exact_point": lower > cap,
        "known_feasible_tiny_candidate_NOT_excluded": True,
        "tiny_candidate_original_whole_box_energy_control": tiny_bound,
        "floating_weight_optimizer_NOT_proof": {
            "success": bool(numerical.success), "message": str(numerical.message),
            "iterations": int(numerical.nit), "old_normalized_energy": base,
            "new_normalized_energy": suggested_energy,
            "old_rod_squared_length_spread": float(np.ptp(base_squared)),
            "new_rod_squared_length_spread": float(np.ptp(suggested_squared)),
        },
        "whole_actual_root_cover_NOT_proved": True,
        "free_vertex_realization_and_continuous_disk_cover_NOT_constructed": True,
        "complete_latest_model_source_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (dirichlet, energy, codec)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "alternative_same_original_rod_support_diagnosis_completed": True,
        "exact_point_strictly_excluded": lower > cap,
        "whole_actual_root_NOT_paid": True, "verified": False, "new_geometric_payments": 0}),
        flush=True)


if __name__ == "__main__":
    main()
