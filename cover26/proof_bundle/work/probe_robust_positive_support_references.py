"""Actual hard-leaf robust weight/reference suggestions, then exact bounds."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_adaptive_signed_support_forest as forest
import n26_broad_positive_support_suggestion as broader
import n26_typed_arithmetic_context as codec
import probe_alternative_signed_hull_forest as signed_suggestion
import probe_candidate_positive_curvature_hull as fixed
import probe_broad_positive_support_leaves as broad_producer
import propose_candidate_curvature_energy as stationary_suggestion
import resume_candidate_adaptive_signed_support_forest as seed_producer
import verify_conditional_force_stage as binding


def feasible_reference(angles, lower, upper, matrix):
    for epsilon in (F(0), F(1, 10**13), F(1, 10**11), F(1, 10**9)):
        candidate = [max(a, min(b, F(round(float(value)*10**15), 10**15)-epsilon))
                     for value, a, b in zip(angles, lower, upper)]
        projected = forest.prior.tighten(matrix, candidate, upper)
        if projected is not None:
            try:
                forest.signed.hull.quadratic.reference_gate(
                    projected[0], lower, upper, matrix)
            except ValueError:
                pass
            else:
                return projected[0]
    midpoint = [(a+b)/2 for a, b in zip(lower, upper)]
    forest.signed.hull.quadratic.reference_gate(midpoint, lower, upper, matrix)
    return midpoint


def test_reference(original, support, box, start, tight, arcs):
    kernel = forest.signed.alternative.kernel_gate(
        original["reference"], support["reference"], support["inverse"])
    angles, numerical = stationary_suggestion.stationary(
        kernel, original["matrix"], *box, start)
    reference = feasible_reference(angles, *box, original["matrix"])
    certificate, diagnostic = signed_suggestion.suggest(
        original, support, box, reference, tight, arcs)
    return {
        "NEW_positive_support": support, "NEW_signed_certificate": certificate,
        "reference_turns": list(map(str, reference)),
        "signed_arithmetic_diagnosis": diagnostic,
        "floating_stationary_suggestion_NOT_proof": numerical,
        "strict_actual_closed_leaf_exclusion": certificate is not None
        and diagnostic["exact_arithmetic_result"]["arithmetic_strict_target_test_passed"],
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "seed", "broader-diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--indices", type=int, nargs="+", default=[514])
    parser.add_argument("--rounds", type=int, default=2)
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
        raise ValueError("robust reference probe changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, seed_digest = binding.read(args.seed), binding.sha(args.seed)
    diagnosis, diagnosis_digest = binding.read(args.broader_diagnosis), binding.sha(args.broader_diagnosis)
    if (seed["schema"] != seed_producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(seed_producer.__file__)
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or diagnosis["old_arithmetic_forest_sha256"] != seed_digest
            or diagnosis["executed_probe_sha256"] != binding.sha(broad_producer.__file__)
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0):
        raise ValueError("robust reference probe changed preserved actual diagnostic/scope")
    source = binding.local_path(seed["actual_latest_candidate_layer_identity_only"][
        "actual_latest_candidate_acceptance"]).parent
    source_accepted = binding.read(source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(source / name) != digest or source_accepted["files"][name] != digest:
            raise ValueError("robust reference probe changed actual source/history DATA")
    arcs = binding.force.load_trig(args.resource)[0]
    row = seed["actual_source_closed_box"]
    actual_row = next(item for item in binding.read(source / "PENDING-ANGLES.json")
                      if item["index"] == seed["source_OPEN_index"])
    if actual_row != row:
        raise ValueError("robust reference probe changed actual whole-root ownership")
    previous, pending, ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (previous != seed["arithmetic_result"] or pending != seed["pending_closed_leaf_boxes"]
            or ledger != seed["arithmetic_ledger"]):
        raise ValueError("old actual root partition and all closed leaves did not reconstruct")
    by_index = {leaf["index"]: leaf for leaf in pending}
    old_trials = {item["old_OPEN_leaf_index"]: item for item in diagnosis["results"]}
    if any(index not in by_index or index not in old_trials for index in args.indices):
        raise ValueError("robust reference probe invented a paid/nonexistent hard OPEN leaf")
    root_box = forest.prior.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    results = []
    for index in args.indices:
        leaf = by_index[index]
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        center = [(a+b)/2 for a, b in zip(*box)]
        tests = [test_reference(original, trial["NEW_positive_support"], box, center, tight, arcs)
                 for trial in old_trials[index]["broader_support_trials"]]
        for round_index in range(args.rounds):
            constructed = [test for test in tests if test["NEW_signed_certificate"] is not None]
            if not constructed:
                break
            best = max(constructed, key=lambda test: F(
                test["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]["strict_radius_margin"]))
            reference = list(map(F, best["reference_turns"]))
            candidates = broader.suggest(original, kernel, reference, iterations=220, log_spread=3)
            for support, _, _ in candidates:
                test = test_reference(original, support, box, reference, tight, arcs)
                test["robust_weight_reference_round"] = round_index+1
                tests.append(test)
            if any(test["strict_actual_closed_leaf_exclusion"] for test in tests):
                break
        strict = [test for test in tests if test["strict_actual_closed_leaf_exclusion"]]
        results.append({
            "old_OPEN_leaf_index": index, "actual_closed_leaf": leaf, "tests": tests,
            "at_least_one_strict_actual_closed_leaf_exclusion": bool(strict),
        })
        print(json.dumps({
            "actual_hard_OPEN_leaf": index, "weight_reference_candidates": len(tests),
            "exact_strict_whole_closed_leaf_exclusion": bool(strict),
            "verified": False, "new_geometric_payments": 0}), flush=True)
    if binding.sha(args.seed) != seed_digest or binding.sha(args.broader_diagnosis) != diagnosis_digest:
        raise ValueError("preserved diagnostics changed during robust reference probes")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(source / name) != digest:
            raise ValueError("actual source/history DATA changed during robust reference probes")
    report = {
        "schema": "N26-unaccepted-robust-positive-weight-reference-leaf-diagnosis-v1",
        "verified": False, "old_arithmetic_forest_sha256": seed_digest,
        "broader_diagnosis_sha256": diagnosis_digest, "results": results,
        "all_old_partition_nodes_and_supports_unmodified": True,
        "whole_actual_root_cover_NOT_proved": True,
        "complete_latest_source_model_history_geometry_gate_NOT_executed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "tested_signed_module_sha256": binding.sha(forest.signed.__file__),
        "broader_suggestion_module_sha256": binding.sha(broader.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"robust_weight_reference_diagnosis_completed": True,
                      "actual_closed_leaves": len(results), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
