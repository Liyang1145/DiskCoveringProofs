"""Primal feasibility versus fresh exact stresses on latest root25 OPEN boxes."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

import n26_pairwise_affine_energy as affine
import n26_typed_arithmetic_context as codec
import probe_balanced_full134rod_minimax as balanced
import probe_full_candidate_face_energy as kernel_producer
import test_full134rod_minimax_relaxation as independent
import verify_conditional_force_stage as binding


def uncovered_witness(points, radius):
    """One exact uncovered point is enough to refute this PARTICULAR cover."""
    centers = [list(map(F, point)) for point in points[:26]]
    numerical = np.array([[float(x), float(y)] for x, y in centers])
    candidates = []
    for ix in range(-30, 31):
        for iy in range(-30, 31):
            if ix*ix+iy*iy <= 900:
                candidates.append((F(ix, 30), F(iy, 30)))
    ordered = sorted(candidates, key=lambda point: float(np.min(np.sum(
        (numerical-np.array([float(v) for v in point]))**2, axis=1))), reverse=True)
    for x, y in ordered[:10]:
        distances = [(x-cx)**2+(y-cy)**2 for cx, cy in centers]
        if x*x+y*y <= 1 and min(distances) > F(radius)**2:
            return {"exact_point": [str(x), str(y)],
                    "exact_unit_disk_margin": str(1-x*x-y*y),
                    "exact_minimum_squared_distance_margin_above_Rstar_upper":
                        str(min(distances)-F(radius)**2)}
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-leaves", type=int, default=3)
    parser.add_argument("--iterations", type=int, default=300)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.max_leaves <= 16:
        raise ValueError("preserve existing primal/stress evidence")
    pilot_path = Path("outputs/n26-latest-root25-pairwise-affine-energy-pilot-v1.json")
    pilot = binding.read(pilot_path)
    digests = dict(pilot["input_sha256"])
    digests[str(pilot_path)] = binding.sha(pilot_path)
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("latest-leaf pilot input association changed")
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    original = codec.gate(binding.read(resource/"CONTEXT.json")["typed_context"])["original"]
    full = balanced.full
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    donor_path = Path("outputs/n26-candidate-root28-grown-full134rod-intersection-forest-diagnosis-v9.json")
    donor = binding.read(donor_path)
    initial_kernel = full.kernel_gate(model, donor["full134rod_supports"][0]["kernel_certificate"])
    del donor
    actual_path = Path("outputs/n26-candidate-root25-checked-support-cost-forest-diagnosis-v3.json")
    actual = binding.read(actual_path)
    pending = {row["index"]: row for row in actual["pending_closed_leaf_boxes"]}
    source_nodes = actual["nodes"]
    del actual
    modules = (affine, balanced, kernel_producer, independent, codec, binding)
    digests.update({module.__file__: binding.sha(module.__file__) for module in modules})
    digests[__file__] = binding.sha(__file__)
    current_path = Path("outputs/n26-twenty-seventh-conditional-final-digest-recheck-v27-sparse-v1-strict-with-owned8.json")
    current = binding.read(current_path)
    digests[str(current_path)] = binding.sha(current_path)
    radius_lower = current["r_strict_interval"][0]
    radius_upper = F(original["radius"])
    if radius_upper != F(current["r_strict_interval"][1]):
        raise ValueError("same-root radius changed")
    arcs = binding.force.load_trig(resource)[0]
    rows = sorted(pilot["results"], key=lambda row: max(
        F(trial["exact_entire_closed_leaf_result"]["normalized_closed_box_energy_lower"])
        for trial in row["trials"] if trial["exact_entire_closed_leaf_result"] is not None))
    chosen = [rows[k*(len(rows)-1)//max(1, args.max_leaves-1)]
              for k in range(args.max_leaves)]
    results = []
    for row in chosen:
        leaf = row["actual_root25_v3_OPEN_leaf"]
        if pending.get(leaf["index"]) != leaf or source_nodes[leaf["index"]] != {"kind": "OPEN"}:
            raise ValueError("not the actual latest retained OPEN box")
        turns = [(F(a)+F(b))/2 for a, b in zip(leaf["lower"], leaf["upper"])]
        full.hull.quadratic.reference_gate(turns, leaf["lower"], leaf["upper"], original["matrix"])
        points, weights, numerical = balanced.balanced_suggestion(
            model, initial_kernel, turns, args.iterations)
        rational = [[str(F(round(float(v)*10**16), 10**16)) for v in point] for point in points]
        exact = balanced.old.exact_relaxation(
            model, original["matrix"], leaf, turns, rational, radius_lower, arcs)
        point_item = {"actual_fixed_feasible_anchor_turns": list(map(str, turns)),
                      "rational60_free_points_NEW134rod_model": rational,
                      "exact_necessary_model_realization_result": exact}
        below = independent.point_controls(original, model, leaf, point_item, radius_lower, arcs)
        certificate, kernel = kernel_producer.exact_kernel(model, weights)
        identity = full.native_graph.identity_control(kernel)
        point_energy = full.hull.quadratic.point_energy_gradient(kernel, [F(0), *turns], arcs)[0]
        normalized_point_lower = point_energy/F(sum(kernel["weights"]), kernel["scale"])
        data = affine.prepare(kernel, original["matrix"], leaf["lower"], leaf["upper"], arcs)
        line_checks = affine.independent_point_checks(data, arcs)
        affine_certificate, affine_result, affine_numerical = affine.suggest(
            data, original["matrix"], radius_upper)
        if below and affine_result is not None and affine_result["arithmetic_strict_entire_closed_leaf"]:
            raise AssertionError("exact feasible primal contradicts the new exact entire-leaf lower bound")
        tiny = original["cap"]["known_candidate_tiny_angle_cells"]
        tiny_data = affine.prepare(kernel, original["matrix"], [p[0] for p in tiny],
                                   [p[1] for p in tiny], arcs)
        _, tiny_result, _ = affine.suggest(tiny_data, original["matrix"], radius_upper)
        if tiny_result is not None and tiny_result["arithmetic_strict_entire_closed_leaf"]:
            raise AssertionError("fresh stress excludes known feasible candidate control")
        witness = uncovered_witness(rational, radius_upper) if below else None
        result = {
            "actual_latest_root25_v3_OPEN_leaf": leaf,
            **point_item,
            "actual_independent_all134rod_point_radius_check_passed": True,
            "fresh_full134rod_positive_stress_kernel_certificate": certificate,
            "fresh_exact_ground_and_square_completion_identity": identity,
            "exact_normalized_fixed_anchor_point_energy_lower": str(normalized_point_lower),
            "exact_fixed_anchor_point_energy_margin_above_Rstar_upper_squared":
                str(normalized_point_lower-radius_upper**2),
            "new_pairwise_affine_certificate": affine_certificate,
            "new_exact_pairwise_entire_leaf_result": affine_result,
            "independent_pair_line_endpoint_midpoint_checks": line_checks,
            "exact_uncovered_unit_disk_point_for_this_primal_only": witness,
            "numerical_minimax_and_stress_fit_NOT_proofs": numerical,
            "numerical_affine_LP_NOT_proof": affine_numerical,
        }
        results.append(result)
        print(json.dumps({
            "actual_latest_root25_OPEN_leaf": leaf["index"],
            "exact_relaxation_radius": exact["exact_outward_realization_radius"],
            "exact_below_Rstar_necessary_model_realization": below,
            "fresh_exact_fixed_point_energy_strict": normalized_point_lower > radius_upper**2,
            "fresh_exact_whole_leaf_strict": affine_result is not None
                and affine_result["arithmetic_strict_entire_closed_leaf"],
            "specific_relaxation_noncover_exact_witness": witness is not None,
            "verified": False, "new_geometric_payments": 0}), flush=True)
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("primal/stress input changed during execution")
    report = {
        "schema": "N26-actual-latest-root25-primal-versus-fresh-stress-experiment-v1",
        "verified": False, "source_OPEN_index": 25,
        "actual_latest_leaves_tested": len(results), "results": results,
        "input_sha256": digests,
        "all_existing_forests_nodes_supports_ledgers_and_payments_UNMODIFIED": True,
        "resource_and_donor_supports_are_arithmetic_DATA_ONLY": True,
        "complete_latest_source_geometry_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
