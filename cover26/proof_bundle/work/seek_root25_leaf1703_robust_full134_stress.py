"""Two targeted stress/reference rounds on one entire actual latest OPEN leaf."""

from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

import n26_typed_arithmetic_context as codec
import probe_balanced_full134rod_minimax as balanced
import probe_full_candidate_face_energy as kernel_producer
import probe_latest_root25_primal_stress as actual_points
import test_full134rod_minimax_relaxation as independent
import verify_conditional_force_stage as binding
from n26_sharp_radius_constraints import SCALE


def worst_reference(kernel, matrix, leaf, start):
    lower, upper = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    free = [k for k, (a, b) in enumerate(zip(lower, upper)) if b-a > F(1, 10**7)]
    initial = np.array([float(start[k]) for k in free])
    pairs = [(i, j, float(F(n, kernel["inverse_denominator"]*sum(kernel["weights"]))))
             for i, j, n in kernel["pairs"]]

    def turns(x):
        result = np.r_[0., [float(value) for value in start]]
        for k, value in zip(free, x):
            result[k+1] = value
        return result

    def objective(x):
        point, gradient, value = turns(x), np.zeros(16), 0.
        for i, j, coefficient in pairs:
            delta = point[j]-point[i]
            value += coefficient*2*(1-np.cos(2*np.pi*delta))
            derivative = coefficient*4*np.pi*np.sin(2*np.pi*delta)
            gradient[i] -= derivative
            gradient[j] += derivative
        return value, gradient[np.array(free)+1]

    directions, constants = [], []
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            row = np.array([float(j == k+1)-float(i == k+1) for k in free])
            fixed = sum((float(j == k+1)-float(i == k+1))*float(start[k])
                        for k in range(15) if k not in free)
            directions.append(row)
            constants.append(float(F(matrix[i][j], SCALE))-fixed)
    directions, constants = np.array(directions), np.array(constants)
    optimized = minimize(
        objective, initial, jac=True, method="SLSQP",
        bounds=[(float(lower[k]), float(upper[k])) for k in free],
        constraints={"type": "ineq", "fun": lambda x: constants-directions@x,
                     "jac": lambda x: -directions},
        options={"maxiter": 300, "ftol": 1e-13, "disp": False})
    hint = list(start)
    for k, value in zip(free, optimized.x):
        hint[k] = F(round(float(value)*10**16), 10**16)
    delta = [b-a for a, b in zip(start, hint)]
    ratios = [F(1)]
    for a, b, point, d in zip(lower, upper, start, delta):
        if d > 0:
            ratios.append((b-point)/d)
        elif d < 0:
            ratios.append((point-a)/(-d))
    framed, framed_delta = [F(0), *start], [F(0), *delta]
    for i in range(16):
        for j in range(16):
            d = framed_delta[j]-framed_delta[i]
            if d > 0:
                ratios.append((F(matrix[i][j], SCALE)-framed[j]+framed[i])/d)
    alpha = max(F(0), min(ratios))*F(999999, 1000000)
    exact = [a+alpha*d for a, d in zip(start, delta)]
    balanced.full.hull.quadratic.reference_gate(exact, lower, upper, matrix)
    return exact, {"numerical_weighted_energy_minimization_NOT_proof": bool(optimized.success),
                   "numerical_weighted_energy_suggestion_NOT_proof": float(optimized.fun),
                   "exact_feasible_segment_fraction": str(alpha)}


def main():
    output = Path("outputs/n26-latest-root25-leaf1703-robust-full134-stress-v1.json")
    if output.exists():
        raise FileExistsError(output)
    input_path = Path("outputs/n26-latest-root25-primal-versus-fresh-stress-v1.json")
    record = binding.read(input_path)
    digests = dict(record["input_sha256"])
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("actual fresh stress input changed")
    digests[str(input_path)] = binding.sha(input_path)
    modules = (balanced, kernel_producer, actual_points, independent, codec, binding)
    digests.update({module.__file__: binding.sha(module.__file__) for module in modules})
    digests[__file__] = binding.sha(__file__)
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    original = codec.gate(binding.read(resource/"CONTEXT.json")["typed_context"])["original"]
    full = balanced.full
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    arcs = binding.force.load_trig(resource)[0]
    item = next(row for row in record["results"]
                if row["actual_latest_root25_v3_OPEN_leaf"]["index"] == 1703)
    leaf = item["actual_latest_root25_v3_OPEN_leaf"]
    latest = binding.read(Path("outputs/n26-candidate-root25-checked-support-cost-forest-diagnosis-v3.json"))
    if (latest["nodes"][1703] != {"kind": "OPEN"}
            or leaf not in latest["pending_closed_leaf_boxes"]):
        raise ValueError("leaf1703 is not the actual latest unresolved closed box")
    del latest
    kernel = full.kernel_gate(model, item["fresh_full134rod_positive_stress_kernel_certificate"])
    reference = list(map(F, item["actual_fixed_feasible_anchor_turns"]))
    radius_lower = binding.read(Path(
        "outputs/n26-twenty-seventh-conditional-final-digest-recheck-v27-sparse-v1-strict-with-owned8.json"
    ))["r_strict_interval"][0]
    helper = balanced.old.prior_producer
    numerical_helper = helper.previous.producer.old_probe
    digests.update({module.__file__: binding.sha(module.__file__)
                    for module in (full, helper, numerical_helper)})
    results = []
    for number in range(2):
        reference, suggestion = worst_reference(kernel, original["matrix"], leaf, reference)
        points, weights, numerical = balanced.balanced_suggestion(model, kernel, reference, 300)
        rational = [[str(F(round(float(v)*10**16), 10**16)) for v in point] for point in points]
        exact = balanced.old.exact_relaxation(
            model, original["matrix"], leaf, reference, rational, radius_lower, arcs)
        point_item = {"actual_fixed_feasible_anchor_turns": list(map(str, reference)),
                      "rational60_free_points_NEW134rod_model": rational,
                      "exact_necessary_model_realization_result": exact}
        below = independent.point_controls(original, model, leaf, point_item, radius_lower, arcs)
        certificate, kernel = kernel_producer.exact_kernel(model, weights)
        tight = [k for k, (a, b) in enumerate(zip(leaf["lower"], leaf["upper"]))
                 if F(b)-F(a) <= F(1, 10**7)]
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        diagonal, diagonal_result = numerical_helper.suggest_bound(
            original, kernel, box, reference, tight, arcs, 16)
        quadratic, result, bound_numerical = None, None, None
        if diagonal is not None:
            quadratic, result, bound_numerical = helper.suggest(
                kernel, original, leaf, diagonal, arcs)
        strict = result is not None and result["arithmetic_strict_target_test_passed"]
        if below and strict:
            raise AssertionError("exact feasible rod model contradicts exact whole-leaf bound")
        witness = actual_points.uncovered_witness(rational, original["radius"]) if below else None
        results.append({
            "round": number+1, "actual_latest_root25_v3_OPEN_leaf": leaf, **point_item,
            "actual_independent_all134rod_point_check_passed": True,
            "fresh_full134rod_kernel_certificate": certificate,
            "fresh_diagonal_certificate": diagonal, "fresh_diagonal_result": diagonal_result,
            "fresh_correlated_certificate": quadratic, "fresh_correlated_result": result,
            "fresh_exact_whole_leaf_strict": strict,
            "exact_uncovered_unit_disk_point_for_this_primal_only": witness,
            "numerical_worst_reference_NOT_proof": suggestion,
            "numerical_minimax_and_stress_NOT_proofs": numerical,
            "numerical_correlated_bound_NOT_proof": bound_numerical,
        })
        print(json.dumps({"actual_latest_root25_OPEN_leaf": 1703, "round": number+1,
                          "exact_below_Rstar_necessary_model_realization": below,
                          "fresh_exact_whole_leaf_strict": strict,
                          "specific_noncover_exact_witness": witness is not None,
                          "verified": False, "new_geometric_payments": 0}), flush=True)
        if below or strict:
            break
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("targeted exact stress input changed")
    report = {
        "schema": "N26-actual-latest-root25-leaf1703-robust-full134-stress-v1",
        "verified": False, "input_sha256": digests, "results": results,
        "all_existing_forests_nodes_supports_ledgers_and_payments_UNMODIFIED": True,
        "no_new_topological_enumeration_batch_started": True,
        "complete_latest_source_geometry_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
