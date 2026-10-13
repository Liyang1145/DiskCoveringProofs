"""Exact broader-support tests on REAL retained OPEN domains; zero payments."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_adaptive_signed_support_forest as forest
import n26_broad_positive_support_suggestion as broader
import n26_typed_arithmetic_context as codec
import probe_alternative_signed_hull_forest as signed_suggestion
import probe_candidate_positive_curvature_hull as fixed
import resume_candidate_adaptive_signed_support_forest as producer
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=4)
    parser.add_argument("--iterations", type=int, default=180)
    parser.add_argument("--log-spread", type=float, default=3.0)
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
        raise ValueError("broader support probe changed zero-source arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    seed, seed_digest = binding.read(args.seed), binding.sha(args.seed)
    if (seed["schema"] != producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(producer.__file__)
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0
            or seed["all_previous_non_OPEN_nodes_and_positive_supports_preserved_identically"] is not True):
        raise ValueError("broader probe changed actual latest diagnostic forest or admission scope")
    for module in (forest, forest.prior, forest.signed):
        if seed["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("broader probe changed the old exact forest arithmetic")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("broader probe changed actual source/root/history DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == seed["source_OPEN_index"])
    if row != seed["actual_source_closed_box"]:
        raise ValueError("broader probe changed entire actual root ownership")
    arcs = binding.force.load_trig(args.resource)[0]
    previous, pending, ledger = forest.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (previous != seed["arithmetic_result"] or pending != seed["pending_closed_leaf_boxes"]
            or ledger != seed["arithmetic_ledger"]):
        raise ValueError("all old real closed nodes and retained OPEN domains did not reconstruct")
    print(json.dumps({"previous_actual_forest_replayed": True, "old_nodes": len(seed["nodes"]),
                      "old_OPEN_leaves": len(pending), "verified": False,
                      "new_geometric_payments": 0}), flush=True)
    root_box = forest.prior.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    results = []
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    for leaf in pending[:args.limit]:
        box = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
        point = [(a+b)/2 for a, b in zip(*box)]
        forest.signed.hull.hull_gate(point, *box, original["matrix"])
        trials = []
        for support, checked, numerical in broader.suggest(
                original, kernel, point, args.iterations, args.log_spread):
            certificate, diagnostic = signed_suggestion.suggest(
                original, support, box, point, tight, arcs)
            positive = forest.prior.direct_bound(
                checked, [a for a, _ in tiny], [b for _, b in tiny], original["radius"], arcs)
            if positive["radius_conditional_whole_angle_box_excluded"]:
                raise AssertionError("broader positive support excludes the feasible tiny candidate")
            trials.append({
                "NEW_positive_support": support, "NEW_signed_certificate": certificate,
                "signed_arithmetic_diagnosis": diagnostic,
                "numerical_suggestion_NOT_proof": numerical,
                "feasible_tiny_candidate_not_excluded": True,
                "strict_actual_closed_leaf_exclusion": certificate is not None
                and diagnostic["exact_arithmetic_result"]["arithmetic_strict_target_test_passed"],
            })
        result = {
            "source_OPEN_index": row["index"], "actual_source_closed_box": row,
            "old_OPEN_leaf_index": leaf["index"], "actual_closed_leaf": leaf,
            "broader_support_trials": trials,
            "at_least_one_strict_actual_closed_leaf_exclusion": any(
                item["strict_actual_closed_leaf_exclusion"] for item in trials),
        }
        results.append(result)
        print(json.dumps({
            "retained_OPEN_leaf_probed": leaf["index"],
            "strict_broader_support_found": result["at_least_one_strict_actual_closed_leaf_exclusion"],
            "trial_strict_flags": [item["strict_actual_closed_leaf_exclusion"] for item in trials],
            "verified": False, "new_geometric_payments": 0}), flush=True)
    if binding.sha(args.seed) != seed_digest:
        raise ValueError("actual old forest changed during broader support probes")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during broader support probes")
    report = {
        "schema": "N26-unaccepted-broader-positive-original-rod-signed-leaf-diagnosis-v1",
        "verified": False, "old_arithmetic_forest_sha256": seed_digest,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "old775nodes_and_all_prior_supports_unchanged": True,
        "results": results, "whole_actual_root_cover_NOT_proved": True,
        "complete_latest_source_model_history_geometry_gate_NOT_executed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "broader_suggestion_module_sha256": binding.sha(broader.__file__),
        "tested_signed_module_sha256": binding.sha(forest.signed.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "broader_support_leaf_diagnosis_completed": True, "actual_leaves": len(results),
        "strict_actual_leaf_proposals": sum(
            item["at_least_one_strict_actual_closed_leaf_exclusion"] for item in results),
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
