"""Zero-payment diagnosis of the new signed-hull arithmetic lemma.

The fixed context is not a current-source/model-replay cache. This probe
checks only its data identity and the actual latest candidate layer identity.
It does not semantically reconstruct all source ownership or old payments.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_signed_hull_energy_minorant as hull
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import SCALE, tighten
import probe_candidate_positive_curvature_hull as curvature_probe
import verify_conditional_force_stage as binding


def suggest_dual(kernel, matrix, reference, lower, upper, gradient, eta):
    ref = np.array(list(map(float, reference)))
    a = np.array([float(x - r) for x, r in zip(lower[1:], reference[1:])])
    c = np.array([float(x - r) for x, r in zip(upper[1:], reference[1:])])
    signed = np.array(list(map(float, eta)))
    midpoint = np.array([float((x + y) / 2) for x, y in gradient[1:]])
    # Negative-curvature coordinates use a concave-quadratic secant only for
    # suggesting the solver's dual. The final check uses the exact minima.
    shifted = midpoint - np.maximum(signed, 0) * (a + c) / 2
    positive = np.maximum(-signed, 0)
    pairs, rows, rhs = [], [], []
    for i in range(kernel["B"]):
        for j in range(kernel["B"]):
            if i == j:
                continue
            row = np.zeros(kernel["B"] - 1)
            if i:
                row[i - 1] -= 1
            if j:
                row[j - 1] += 1
            rows.append(row)
            rhs.append(float(F(matrix[i][j], SCALE)) - (ref[j] - ref[i]))
            pairs.append((i, j))
    rows, rhs = np.array(rows), np.array(rhs)
    optimized = minimize(
        lambda d: float(shifted @ d + np.dot(positive, d*d) / 2),
        (a + c) / 2,
        jac=lambda d: shifted + positive * d,
        bounds=list(zip(a, c)),
        constraints={"type": "ineq", "fun": lambda d: rhs - rows @ d,
                     "jac": lambda d: -rows},
        method="SLSQP", options={"ftol": 1e-14, "maxiter": 200, "disp": False})
    tangent = shifted + positive * optimized.x
    lp = linprog(tangent, A_ub=rows, b_ub=rhs,
                 bounds=list(zip(a, c)), method="highs")
    q, terms = 10**30, []
    if lp.success:
        for (i, j), multiplier in zip(pairs, lp.ineqlin.marginals):
            numerator = max(0, round(-float(multiplier) * q))
            if numerator:
                terms.append([i, j, str(numerator)])
    return {"q": q, "terms": terms}, {
        "floating_quadratic_solver_success_not_proof": bool(optimized.success),
        "floating_tangent_LP_success_not_proof": bool(lp.success),
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "curvature-diagnosis", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--leaves-per-root", type=int, default=12)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (
        binding.sha(args.resource / "VERIFIED.json") != curvature_probe.RESOURCE_SHA
        or binding.sha(args.resource_replay) != curvature_probe.RESOURCE_SHA
        or binding.read(args.resource_replay) != resource
        or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
        or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
    ):
        raise ValueError("signed-hull diagnosis changed the zero-source arithmetic resource")
    for name in ("CONTEXT.json", "n26_typed_arithmetic_context.py"):
        if binding.sha(args.resource / name) != resource["files"][name]:
            raise ValueError("signed-hull diagnosis changed fixed model/codec bytes")
    if binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]:
        raise ValueError("signed-hull diagnosis executed a different typed codec")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("signed-hull diagnosis changed the exact current radius")
    diagnosis = binding.read(args.curvature_diagnosis)
    if (
        diagnosis["verified"] is not False
        or diagnosis["new_geometric_payments"] != 0
        or diagnosis["actual_current_audit_sha256"] != current_digest
        or diagnosis["executed_probe_sha256"] != binding.sha(curvature_probe.__file__)
    ):
        raise ValueError("signed-hull diagnosis has incompatible curvature suggestions")
    pending = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    accepted = binding.read(args.source / "VERIFIED.json")
    leaves_path = args.source / "PENDING-FOREST-LEAVES.json"
    if binding.sha(leaves_path) != accepted["files"][leaves_path.name]:
        raise ValueError("signed-hull diagnosis changed the current leaf-box data")
    leaves = {row["source_OPEN_index"]: row["retained_closed_leaf_boxes"]
              for row in binding.read(leaves_path)}
    reference = list(map(F, diagnosis["reference_turns"]))
    arcs = binding.force.load_trig(args.resource)[0]
    results = []
    for suggestion in diagnosis["results"]:
        root = suggestion["source_OPEN_index"]
        if pending.get(root) != suggestion["actual_source_closed_box"]:
            raise ValueError("signed-hull diagnosis changed the actual latest full-root row")
        if not suggestion["exact_signed_diagonal_curvature_check_passed"]:
            continue
        eta = [F(suggestion["fixed_anchor_negative_allowance"])] * 10 + [
            -F(suggestion["last_five_positive_curvature"])] * 5
        row = pending[root]
        targets = [("whole-root", root, row["sharp_lower"], row["sharp_upper"])]
        targets.extend(
            ("retained-OPEN-leaf", leaf["index"], leaf["lower"], leaf["upper"])
            for leaf in leaves.get(root, [])[:args.leaves_per_root])
        for kind, index, lower, upper in targets:
            box = tighten(original["matrix"], lower, upper)
            if box is None:
                raise ValueError("a retained diagnostic target has an empty sharp domain")
            lower, upper = box
            ref, lo, hi, _, _ = hull.hull_gate(
                reference, lower, upper, original["matrix"])
            _, gradient = hull.outward_point_values(kernel, ref, arcs)
            dual, numerical = suggest_dual(
                kernel, original["matrix"], ref, lo, hi, gradient, eta)
            certificate = {
                "reference_turns": list(map(str, reference)),
                "signed_eta": list(map(str, eta)), "difference_dual": dual}
            check = hull.bound(
                kernel, original["matrix"], lower, upper, certificate,
                original["radius"], arcs)
            # The zero-dual alternative cannot be worse due to a noisy solver.
            zero = {**certificate, "difference_dual": {"q": 1, "terms": []}}
            zero_check = hull.bound(
                kernel, original["matrix"], lower, upper, zero,
                original["radius"], arcs)
            if F(zero_check["minimum_strict_energy_margin"]) > F(
                    check["minimum_strict_energy_margin"]):
                certificate, check = zero, zero_check
            results.append({
                "source_OPEN_index": root, "diagnostic_target_kind": kind,
                "target_index": index, "closed_sharp_lower": list(map(str, lower)),
                "closed_sharp_upper": list(map(str, upper)),
                "certificate": certificate, "arithmetic_result": check, **numerical})
            print(json.dumps({
                "root": root, "target": index, "kind": kind,
                "arithmetic_strict_test": check["arithmetic_strict_exclusion_test_passed"],
                "exact_energy_margin_display": float(F(check["minimum_strict_energy_margin"])),
                "verified": False, "new_geometric_payments": 0}), flush=True)
    # Feasible tiny candidate must not satisfy a strict exclusion test.
    tiny = [tuple(map(F, pair))
            for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    lo, hi = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
    controls = []
    for suggestion in diagnosis["results"]:
        if not suggestion["exact_signed_diagonal_curvature_check_passed"]:
            continue
        cert = {
            "reference_turns": list(map(str, reference)),
            "signed_eta": [suggestion["fixed_anchor_negative_allowance"]] * 10 + [
                str(-F(suggestion["last_five_positive_curvature"]))] * 5,
            "difference_dual": {"q": 1, "terms": []}}
        result = hull.bound(kernel, original["matrix"], lo, hi, cert, original["radius"], arcs)
        if result["arithmetic_strict_exclusion_test_passed"]:
            raise AssertionError("signed-hull diagnosis falsely excludes the known tiny candidate")
        controls.append({"suggestion_root": suggestion["source_OPEN_index"],
                         "feasible_tiny_strict_test_false": True})
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("current audit changed during signed-hull diagnosis")
    report = {
        "schema": "N26-unaccepted-signed-hull-energy-diagnosis-v1",
        "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "fixed_arithmetic_resource_acceptance_sha256": curvature_probe.RESOURCE_SHA,
        "curvature_diagnosis_sha256": binding.sha(args.curvature_diagnosis),
        "source_leaf_box_data_sha256": binding.sha(leaves_path),
        "arithmetic_targets_checked": len(results),
        "arithmetic_strict_tests_passed": sum(
            row["arithmetic_result"]["arithmetic_strict_exclusion_test_passed"] for row in results),
        "feasible_tiny_positive_controls": controls, "results": results,
        "full_latest_source_model_ownership_replay_not_performed": True,
        "all_historical_resource_dependencies_not_rehashed_here": True,
        "independent_frozen_standalone_acceptance_and_actual_replay_still_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (hull, hull.quadratic, codec, identity, binding)},
        "arithmetic_lemma_sha256": binding.sha(Path(__file__).with_name(
            "n26-signed-hull-energy-minorant-proof.md")),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("results", "modules")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
