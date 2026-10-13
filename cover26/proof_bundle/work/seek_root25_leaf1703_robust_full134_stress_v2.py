"""Version2: exact DBM projection, retaining the zero-move version1 failure."""

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
    pairs = [(i, j, float(F(n, kernel["inverse_denominator"]*sum(kernel["weights"]))))
             for i, j, n in kernel["pairs"]]

    def framed(x):
        point = np.r_[0., [float(value) for value in start]]
        for k, value in zip(free, x):
            point[k+1] = value
        return point

    def objective(x):
        point, gradient, value = framed(x), np.zeros(16), 0.
        for i, j, coefficient in pairs:
            delta = point[j]-point[i]
            value += coefficient*2*(1-np.cos(2*np.pi*delta))
            derivative = coefficient*4*np.pi*np.sin(2*np.pi*delta)
            gradient[i] -= derivative
            gradient[j] += derivative
        return value, gradient[np.array(free)+1]

    rows, rhs = [], []
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            row = np.array([float(j == k+1)-float(i == k+1) for k in free])
            fixed = sum((float(j == k+1)-float(i == k+1))*float(start[k])
                        for k in range(15) if k not in free)
            rows.append(row)
            rhs.append(float(F(matrix[i][j], SCALE))-fixed)
    rows, rhs = np.array(rows), np.array(rhs)
    optimized = minimize(
        objective, np.array([float(start[k]) for k in free]), jac=True, method="SLSQP",
        bounds=[(float(lower[k]), float(upper[k])) for k in free],
        constraints={"type": "ineq", "fun": lambda x: rhs-rows@x,
                     "jac": lambda x: -rows},
        options={"maxiter": 300, "ftol": 1e-13, "disp": False})
    hints = list(start)
    for k, value in zip(free, optimized.x):
        hints[k] = F(round(float(value)*10**16), 10**16)
    contractor = balanced.old.prior_producer.previous.producer.latest_controls.producer.BASE
    box = contractor.tighten(matrix, lower, upper)
    order = sorted(free, key=lambda k: abs(hints[k]-start[k]), reverse=True)
    order += [k for k in range(15) if k not in free]
    choices = []
    for axis in order:
        a, b = map(list, box)
        proposed = min(b[axis], max(a[axis], hints[axis]))
        a[axis] = b[axis] = proposed
        next_box = contractor.tighten(matrix, a, b)
        other = contractor.independently_contract(matrix, a, b)
        fallback = False
        if next_box is None:
            a, b = map(list, box)
            proposed = (a[axis]+b[axis])/2
            a[axis] = b[axis] = proposed
            next_box = contractor.tighten(matrix, a, b)
            other = contractor.independently_contract(matrix, a, b)
            fallback = True
        if next_box is None or next_box != other:
            raise ValueError("exact sequential feasible-reference contraction failed")
        box = next_box
        choices.append({"axis": axis, "exact_value": str(proposed),
                        "hint_clipped_to_current_exact_projection": proposed != hints[axis],
                        "midpoint_fallback": fallback})
    if box[0] != box[1]:
        raise ValueError("exact reference projection did not fix every coordinate")
    point = box[0]
    balanced.full.hull.quadratic.reference_gate(point, lower, upper, matrix)
    return point, {
        "numerical_weighted_energy_minimization_NOT_proof": bool(optimized.success),
        "numerical_weighted_energy_suggestion_NOT_proof": float(optimized.fun),
        "exact_reference_actually_changed": point != start,
        "exact_maximum_reference_change": str(max(abs(a-b) for a, b in zip(point, start))),
        "every_exact_coordinate_choice_and_independent_contraction": choices,
    }


def main():
    output = Path("outputs/n26-latest-root25-leaf1703-robust-full134-stress-v2.json")
    if output.exists():
        raise FileExistsError(output)
    input_path = Path("outputs/n26-latest-root25-primal-versus-fresh-stress-v1.json")
    record = binding.read(input_path)
    digests = dict(record["input_sha256"])
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("actual latest inputs changed")
    digests[str(input_path)] = binding.sha(input_path)
    digests[__file__] = binding.sha(__file__)
    failure = Path("outputs/n26-latest-root25-leaf1703-robust-full134-stress-v1.json")
    digests[str(failure)] = binding.sha(failure)
    modules = (balanced, kernel_producer, actual_points, independent, codec, binding)
    digests.update({module.__file__: binding.sha(module.__file__) for module in modules})
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    original = codec.gate(binding.read(resource/"CONTEXT.json")["typed_context"])["original"]
    full = balanced.full
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    arcs = binding.force.load_trig(resource)[0]
    item = next(row for row in record["results"]
                if row["actual_latest_root25_v3_OPEN_leaf"]["index"] == 1703)
    leaf = item["actual_latest_root25_v3_OPEN_leaf"]
    latest = binding.read(Path("outputs/n26-candidate-root25-checked-support-cost-forest-diagnosis-v3.json"))
    if latest["nodes"][1703] != {"kind": "OPEN"} or leaf not in latest["pending_closed_leaf_boxes"]:
        raise ValueError("not the actual newest OPEN leaf")
    del latest
    kernel = full.kernel_gate(model, item["fresh_full134rod_positive_stress_kernel_certificate"])
    reference = list(map(F, item["actual_fixed_feasible_anchor_turns"]))
    final_path = Path("outputs/n26-twenty-seventh-conditional-final-digest-recheck-v27-sparse-v1-strict-with-owned8.json")
    digests[str(final_path)] = binding.sha(final_path)
    radius_lower = binding.read(final_path)["r_strict_interval"][0]
    helper = balanced.old.prior_producer
    numerical_helper = helper.previous.producer.old_probe
    contractor = helper.previous.producer.latest_controls.producer.BASE
    digests.update({module.__file__: binding.sha(module.__file__)
                    for module in (full, helper, numerical_helper, contractor)})
    results = []
    for number in range(2):
        reference, suggestion = worst_reference(kernel, original["matrix"], leaf, reference)
        if not suggestion["exact_reference_actually_changed"]:
            raise ValueError("zero-move reference is not an actual worst-reference round")
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
            quadratic, result, bound_numerical = helper.suggest(kernel, original, leaf, diagonal, arcs)
        strict = result is not None and result["arithmetic_strict_target_test_passed"]
        if below and strict:
            raise AssertionError("exact primal and exact entire-leaf lower bound disagree")
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
                          "exact_reference_actually_changed": True,
                          "exact_below_Rstar_necessary_model_realization": below,
                          "fresh_exact_whole_leaf_strict": strict,
                          "specific_noncover_exact_witness": witness is not None,
                          "verified": False, "new_geometric_payments": 0}), flush=True)
        if below or strict:
            break
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("exact-projection experiment input changed")
    report = {
        "schema": "N26-actual-latest-root25-leaf1703-robust-full134-stress-v2",
        "verified": False, "input_sha256": digests, "results": results,
        "version1_zero_segment_failure_preserved_not_counted_as_actual_reference_motion": True,
        "all_existing_forests_nodes_supports_ledgers_and_payments_UNMODIFIED": True,
        "complete_latest_source_geometry_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
