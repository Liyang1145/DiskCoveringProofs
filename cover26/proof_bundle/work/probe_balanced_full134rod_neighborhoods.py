"""Proper closed source-leaf neighborhoods with checked NEW134rod stresses."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_balanced_full134rod_minimax as stress_producer
import test_balanced_full134rod_minimax as stress_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-balanced-full134rod-proper-neighborhood-energy-v1"
full = stress_producer.full


def data_gate(args):
    original, model, seed, ancestor, prior, row, arcs, digests, layer = stress_producer.old.prior_producer.input_gate(args)
    for path in (args.old_minimax_diagnosis, args.old_minimax_controls, args.correlated_diagnosis,
                 args.correlated_controls, args.balanced_diagnosis, args.balanced_controls):
        digests[path] = binding.sha(path)
    old_record = binding.read(args.old_minimax_diagnosis)
    record, controls = binding.read(args.balanced_diagnosis), binding.read(args.balanced_controls)
    stress_controls.scope_gate(record, seed, row, model, layer, old_record, args, digests)
    if (controls["schema"] != stress_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(stress_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.balanced_diagnosis]
            or controls["tested_balanced_probe_sha256"] != binding.sha(stress_producer.__file__)
            or controls["tested_independent_point_stress_module_sha256"] != binding.sha(stress_producer.old_controls.__file__)
            or len(controls["actual_point_radius_stress_rejection_controls_passed"]) != 16
            or len(controls["actual_balanced_executor_source_scope_rejection_controls_passed"]) != 8
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0
            or controls["source_file_sha256"] != seed["source_file_sha256"]):
        raise ValueError("proper neighborhood probe lacks actual balanced fullface independent controls")
    return original, model, seed, row, arcs, digests, layer, record


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "correlated-diagnosis", "correlated-controls",
                 "old-minimax-diagnosis", "old-minimax-controls",
                 "balanced-diagnosis", "balanced-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, row, arcs, digests, layer, record = data_gate(args)
    base = stress_producer.old.prior_producer.previous.producer.latest_controls.producer.BASE
    root_box = base.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    results = []
    for item in record["results"]:
        leaf, turns = item["actual_checked_v7_OPEN_leaf"], list(map(F, item["actual_fixed_feasible_anchor_turns"]))
        kernel, identity = stress_producer.old.prior_producer.previous.arithmetic.kernel_controls(
            model, item["NEW_full134rod_stress_kernel_certificate"])
        point_lower = full.hull.quadratic.point_energy_gradient(kernel, [F(0), *turns], arcs)[0]
        cap = F(original["radius"])**2*F(sum(kernel["weights"]), kernel["scale"])
        trials = []
        for width in (F(1, 1000), F(1, 100000), F(1, 10000000)):
            lower = [max(F(a), turn-width) for a, turn in zip(leaf["lower"], turns)]
            upper = [min(F(b), turn+width) for b, turn in zip(leaf["upper"], turns)]
            box = base.tighten(original["matrix"], lower, upper)
            if box is None:
                raise ValueError("proper closed neighborhood lost its actual feasible reference")
            full.hull.quadratic.reference_gate(turns, *box, original["matrix"])
            if (list(box[0]) == list(map(F, leaf["lower"]))
                    and list(box[1]) == list(map(F, leaf["upper"]))):
                raise ValueError("supplement target was falsely declared a proper sub-neighborhood")
            diagonal, diagonal_result = stress_producer.old.prior_producer.previous.producer.old_probe.suggest_bound(
                original, kernel, box, turns, tight, arcs, 16)
            certificate, result = None, None
            if diagonal is not None:
                target = {"lower": list(map(str, box[0])), "upper": list(map(str, box[1]))}
                certificate, result, _ = stress_producer.old.prior_producer.suggest(
                    kernel, original, target, diagonal, arcs)
            trials.append({
                "requested_closed_half_width": str(width),
                "actual_proper_closed_lower": list(map(str, box[0])),
                "actual_proper_closed_upper": list(map(str, box[1])),
                "NEW_stress_diagonal_certificate": diagonal,
                "NEW_stress_diagonal_result": diagonal_result,
                "NEW_stress_correlated_certificate": certificate,
                "NEW_stress_correlated_result": result,
                "strict_actual_proper_closed_neighborhood":
                    result is not None and result["arithmetic_strict_target_test_passed"],
            })
            print(json.dumps({"checked_v7_leaf": leaf["index"], "proper_half_width": str(width),
                              "exact_strict_proper_closed_neighborhood": trials[-1]["strict_actual_proper_closed_neighborhood"],
                              "NOT_whole_old_leaf_or_root": True,
                              "verified": False, "new_geometric_payments": 0}), flush=True)
        results.append({
            "actual_checked_v7_OPEN_leaf": leaf,
            "actual_fixed_feasible_anchor_turns": list(map(str, turns)),
            "NEW_full134rod_stress_kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
            "NEW_full134rod_stress_exact_identity_controls": identity,
            "exact_fixed_point_energy_lower": str(point_lower),
            "exact_NEWweight_same_root_energy_cap": str(cap),
            "exact_fixed_point_strict_energy_margin": str(point_lower-cap),
            "trials": trials,
        })
    stress_producer.old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "source_file_sha256": seed["source_file_sha256"],
        "checked_v7_forest_sha256": digests[args.seed],
        "actual_current_audit_sha256": digests[args.current_audit],
        "actual_latest_candidate_layer_identity_only": layer,
        "balanced_stress_diagnosis_sha256": digests[args.balanced_diagnosis],
        "balanced_stress_actual_independent_controls_sha256": digests[args.balanced_controls],
        "NEW_distinct_full134rod_edges": model["edges"], "results": results,
        "only_proper_closed_neighborhoods_NOT_whole_old_leaf_or_root": True,
        "old_and_NEWEST_running_forests_supports_NONOPEN_proofs_and_ledgers_UNMODIFIED": True,
        "successful_v7_neighborhood_NEEDS_fresh_actual_v8_OPEN_intersections_and_remaining_cover": True,
        "independent_actual_neighborhood_arithmetic_controls_still_required": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (full, stress_producer, stress_controls, stress_producer.old.prior_producer)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_balanced_full134rod_proper_neighborhood_probe_completed": True,
                      "proper_neighborhoods": sum(len(item["trials"]) for item in results),
                      "strict_proper_neighborhoods": sum(trial["strict_actual_proper_closed_neighborhood"]
                                                       for item in results for trial in item["trials"]),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
