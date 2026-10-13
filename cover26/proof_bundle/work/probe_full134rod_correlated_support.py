"""Fresh correlated bounds on preserved checked v7 leaves while v8 runs.

No latest forest is edited. An old-leaf supplement is not a newest forest
payment; successful certificates need fresh actual newest descendants.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

from audit_prefix_partition import linux
import n26_full134rod_correlated_quadratic_energy as correlated
from n26_sharp_radius_constraints import SCALE
import test_newest_full134rod_robust_descendants as previous
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-distinct-full134rod-correlated-supplemental-energy-v1"


def suggest(kernel, original, leaf, old_certificate, arcs):
    certificate = {
        "schema": correlated.SCHEMA,
        "reference_turns": old_certificate["reference_turns"],
        "parts": old_certificate["parts"],
        "curvature_correction": [str(max(F(0), F(value))) for value in old_certificate["signed_eta"]],
        "quadratic_support_point": ["0"]*15,
        "difference_dual": {"q": 1, "terms": []},
    }
    data = correlated.quadratic_data(
        kernel, original["matrix"], leaf["lower"], leaf["upper"], certificate, arcs)
    a, b = np.array(list(map(float, data["lower_delta"]))), np.array(list(map(float, data["upper_delta"])))
    widths = b-a
    q = np.array([[float(value) for value in row] for row in data["quadratic"]])
    p = np.array(list(map(float, data["linear"])))
    ref = data["reference"]
    pairs, rows, rhs = [], [], []
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            row = np.zeros(15)
            if i:
                row[i-1] -= 1
            if j:
                row[j-1] += 1
            pairs.append((i, j))
            rows.append(row)
            rhs.append(float(F(original["matrix"][i][j], SCALE)-(ref[j]-ref[i])))
    rows, rhs = np.array(rows), np.array(rhs)
    scaled = rows*widths
    scaled_rhs = rhs-rows@a
    scales = np.maximum(np.maximum(np.max(np.abs(scaled), axis=1), np.abs(scaled_rhs)), 1e-12)
    scaled, scaled_rhs = scaled/scales[:, None], scaled_rhs/scales
    initial = np.array([0. if width == 0 else np.clip(-left/width, 0., 1.)
                        for left, width in zip(a, widths)])
    bounds = [(0., 0. if width == 0 else 1.) for width in widths]
    objective_scale = 10**8

    def value(t):
        delta = a+widths*t
        return float((p@delta+delta@q@delta/2)*objective_scale)

    optimized = minimize(
        value, initial, jac=lambda t: widths*(p+q@(a+widths*t))*objective_scale,
        bounds=bounds, constraints={"type": "ineq",
                                   "fun": lambda t: scaled_rhs-scaled@t,
                                   "jac": lambda t: -scaled},
        method="SLSQP", options={"ftol": 1e-12, "maxiter": 400, "disp": False})
    proposed = a+widths*optimized.x
    if not np.all(np.isfinite(proposed)):
        proposed = np.zeros(15)
    point = [F(round(float(value)*10**15), 10**15) for value in proposed]
    exact_tangent = [linear+sum(row[j]*point[j] for j in range(15))
                     for linear, row in zip(data["linear"], data["quadratic"])]
    tangent = np.array(list(map(float, exact_tangent)))
    lp = linprog(widths*tangent*objective_scale, A_ub=scaled, b_ub=scaled_rhs,
                 bounds=bounds, method="highs")
    denominator, terms = 10**30, []
    if lp.success:
        for (i, j), multiplier, scale in zip(pairs, lp.ineqlin.marginals, scales):
            numerator = max(0, round(-float(multiplier)*denominator/(objective_scale*float(scale))))
            if numerator:
                terms.append([i, j, str(numerator)])
    candidates = []
    for label, z, dual in (
        ("zero-tangent-retained-valid-dual", [F(0)]*15, old_certificate["difference_dual"]),
        ("correlated-tangent-zero-dual", point, {"q": 1, "terms": []}),
        ("correlated-tangent-fresh-scaled-LP-dual", point, {"q": denominator, "terms": terms}),
        ("correlated-tangent-retained-valid-dual", point, old_certificate["difference_dual"]),
    ):
        candidate = {**deepcopy(certificate), "quadratic_support_point": list(map(str, z)),
                     "difference_dual": deepcopy(dual)}
        support = correlated.correlated_support(
            {**data, "support_point": z}, original["matrix"], dual)[0]
        candidates.append((support, label, candidate))
    _, selected_label, selected = max(candidates, key=lambda item: item[0])
    result = correlated.bound(
        kernel, original["matrix"], leaf["lower"], leaf["upper"], selected, original["radius"], arcs)
    return selected, result, {
        "numerical_correlated_QP_success_NOT_proof": bool(optimized.success),
        "numerical_correlated_QP_message": str(optimized.message),
        "numerical_correlated_QP_iterations": int(optimized.nit),
        "numerical_tangent_LP_success_NOT_proof": bool(lp.success),
        "selected_exact_support_strategy": selected_label,
        "arbitrary_rational_support_point_NOT_an_assumed_feasible_minimizer": True,
        "exact_candidate_supports": [{"strategy": label, "support_lower": str(support)}
                                     for support, label, _ in candidates],
    }


def input_gate(args):
    original, model, seed, ancestor, old, row, arcs, digests, layer = previous.producer.data_gate(args)
    record = binding.read(args.prior_diagnosis)
    controls = binding.read(args.prior_controls)
    digests[args.prior_diagnosis] = binding.sha(args.prior_diagnosis)
    digests[args.prior_controls] = binding.sha(args.prior_controls)
    previous.scope_gate(record, seed, ancestor, model, args, digests)
    if (controls["schema"] != previous.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(previous.__file__)
            or controls["diagnosis_sha256"] != digests[args.prior_diagnosis]
            or controls["checked_newest_forest_sha256"] != digests[args.seed]
            or controls["checked_newest_forest_controls_sha256"] != digests[args.seed_controls]
            or controls["tested_newest_probe_sha256"] != binding.sha(previous.producer.__file__)
            or controls["tested_NEW_full134rod_module_sha256"] != binding.sha(correlated.full.__file__)
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["candidate_whole_roots_removed"] != 0
            or len(controls["actual_NEW134rod_mode_rejection_controls_passed"]) != 20
            or len(controls["actual_newest_descendant_scope_rejection_controls_passed"]) != 8
            or controls["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("correlated probe lacks actual independent full134rod leaf/source controls")
    return original, model, seed, ancestor, record, row, arcs, digests, layer


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, ancestor, prior, row, arcs, digests, layer = input_gate(args)
    results = []
    for item in prior["results"]:
        leaf, trials = item["actual_newest_OPEN_leaf"], []
        for trial in item["trials"]:
            if trial["NEW_full134rod_energy_certificate"] is None:
                continue
            kernel, identity = previous.arithmetic.kernel_controls(
                model, trial["NEW_full134rod_kernel_certificate"])
            certificate, result, numerical = suggest(
                kernel, original, leaf, trial["NEW_full134rod_energy_certificate"], arcs)
            trials.append({
                "original_checked_strategy": trial["strategy"],
                "NEW_full134rod_kernel_certificate": trial["NEW_full134rod_kernel_certificate"],
                "NEW_full134rod_exact_identity_controls": identity,
                "NEW_correlated_quadratic_certificate": certificate,
                "NEW_correlated_exact_closed_leaf_result": result,
                "strict_actual_checked_v7_closed_leaf_supplement": result["arithmetic_strict_target_test_passed"],
                "old_diagonal_exact_closed_leaf_result": trial["NEW_full134rod_exact_closed_leaf_result"],
                "exact_energy_lower_improvement_over_old_diagonal": str(
                    F(result["boundary_full134rod_correlated_energy_lower"])-
                    F(trial["NEW_full134rod_exact_closed_leaf_result"]["boundary_full134rod_energy_lower"])),
                "numerical_suggestions_NOT_proofs": numerical,
            })
            print(json.dumps({"checked_v7_leaf": leaf["index"], "strategy": trial["strategy"],
                              "NEW_exact_correlated_whole_leaf_strict": result["arithmetic_strict_target_test_passed"],
                              "verified": False, "new_geometric_payments": 0}), flush=True)
        results.append({"actual_checked_v7_OPEN_leaf": leaf,
                        "retained_v6_OPEN_ancestor": item["retained_old_OPEN_ancestor"],
                        "trials": trials})
    previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": row["index"],
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "checked_v7_forest_sha256": digests[args.seed],
        "checked_v7_forest_controls_sha256": digests[args.seed_controls],
        "prior_full134rod_leaf_diagnosis_sha256": digests[args.prior_diagnosis],
        "prior_full134rod_actual_independent_controls_sha256": digests[args.prior_controls],
        "actual_current_audit_sha256": digests[args.current_audit],
        "actual_latest_candidate_layer_identity_only": layer,
        "results": results, "NEW_distinct_full134rod_edges": model["edges"],
        "checked_v7_and_NEWEST_running_v8_forests_nonOPEN_proofs_supports_and_ledgers_UNMODIFIED": True,
        "successful_v7_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction_before_reuse": True,
        "old_diagonal_full134rod_backend_and_original92rod_LOCAL_model_UNMODIFIED": True,
        "whole_actual_root_cover_NOT_proved": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "independent_correlated_arithmetic_controls_still_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (correlated, correlated.full, previous, previous.producer)},
        "arithmetic_lemma_sha256": binding.sha(Path(__file__).with_name(
            "n26-full134rod-correlated-quadratic-proof.md")),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"distinct_full134rod_correlated_probe_completed": True,
                      "actual_v7_leaves": len(results),
                      "exact_correlated_trials": sum(len(item["trials"]) for item in results),
                      "strict_v7_leaf_trials": sum(trial["strict_actual_checked_v7_closed_leaf_supplement"]
                                                  for item in results for trial in item["trials"]),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
