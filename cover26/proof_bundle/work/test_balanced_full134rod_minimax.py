"""Own balanced-objective identity and independent actual point/stress replay."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_balanced_full134rod_minimax as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-balanced-full134rod-minimax-controls-v1"


def scope_gate(record, seed, row, model, layer, old_record, args, digests):
    if (record["schema"] != producer.SCHEMA
            or record["executed_probe_sha256"] != binding.sha(producer.__file__)
            or record["checked_v7_forest_sha256"] != digests[args.seed]
            or record["checked_v7_forest_controls_sha256"] != digests[args.seed_controls]
            or record["old_minimax_diagnosis_sha256"] != digests[args.old_minimax_diagnosis]
            or record["old_minimax_actual_independent_controls_sha256"] != digests[args.old_minimax_controls]
            or record["actual_current_audit_sha256"] != digests[args.current_audit]
            or record["actual_latest_candidate_layer_identity_only"] != layer
            or record["source_OPEN_index"] != row["index"] or record["actual_source_closed_box"] != row
            or record["source_file_sha256"] != seed["source_file_sha256"]
            or record["NEW_distinct_full134rod_edges"] != model["edges"]
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["old_numerical_data_reports_and_NEWEST_running_FORESTS_UNMODIFIED"] is not True
            or record["successful_v7_stress_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction"] is not True
            or record["continuous_disk_cover_and_global_optimality_counterexample_NOT_proved"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True):
        raise ValueError("actual balanced minimax changed own source/history/executor or proof scope")
    for module in (producer.old, producer.old_controls, producer.full,
                   producer.old.prior_producer, producer.old.prior_producer.correlated):
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("actual balanced minimax imported arithmetic changed")
    incoming = {item["actual_checked_v7_OPEN_leaf"]["index"]: item for item in old_record["results"]}
    seen = set()
    for item in record["results"]:
        leaf = item["actual_checked_v7_OPEN_leaf"]
        if (leaf["index"] in seen or leaf != incoming[leaf["index"]]["actual_checked_v7_OPEN_leaf"]
                or item["actual_fixed_feasible_anchor_turns"] != incoming[leaf["index"]]["actual_fixed_feasible_anchor_turns"]
                or item["numerical_minimax_and_equilibrium_suggestions_NOT_proofs"]["numerical_objective_scale"] != 1):
            raise ValueError("balanced replay changed, repeated or relabelled its actual fixed-anchor case")
        seen.add(leaf["index"])
    if seen != set(incoming):
        raise ValueError("balanced replay omitted an entire actual old case")


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
                 "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
                 "prior-controls", "correlated-diagnosis", "correlated-controls",
                 "old-minimax-diagnosis", "old-minimax-controls", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, ancestor, prior, row, arcs, digests, layer = producer.old.prior_producer.input_gate(args)
    for path in (args.old_minimax_diagnosis, args.old_minimax_controls, args.correlated_diagnosis,
                 args.correlated_controls, args.diagnosis):
        digests[path] = binding.sha(path)
    old_record, old_controls = binding.read(args.old_minimax_diagnosis), binding.read(args.old_minimax_controls)
    if (old_record["schema"] != producer.old.SCHEMA
            or old_record["executed_probe_sha256"] != binding.sha(producer.old.__file__)
            or old_controls["schema"] != producer.old_controls.SCHEMA
            or old_controls["executed_test_sha256"] != binding.sha(producer.old_controls.__file__)
            or old_controls["diagnosis_sha256"] != digests[args.old_minimax_diagnosis]
            or old_controls["tested_minimax_probe_sha256"] != binding.sha(producer.old.__file__)
            or len(old_controls["actual_point_dimension_radius_scope_and_fresh_stress_rejection_controls_passed"]) != 16
            or old_controls["verified"] is not False or old_controls["new_geometric_payments"] != 0):
        raise ValueError("balanced independent test lacks actual old minimax controls")
    record = binding.read(args.diagnosis)
    scope_gate(record, seed, row, model, layer, old_record, args, digests)
    radius_lower = binding.read(args.current_audit)["r_strict_interval"][0]
    checked = []
    for item in record["results"]:
        below, kernel = producer.old_controls.trial_controls(original, model, item, radius_lower, arcs)
        checked.append({"checked_v7_OPEN_leaf": item["actual_checked_v7_OPEN_leaf"]["index"],
                        "exact_radius": item["exact_necessary_model_realization_result"]["exact_outward_realization_radius"],
                        "exact_below_Rstar_full134rod_NECESSARY_model_realization": below,
                        "fresh_balanced_stress_correlated_whole_leaf_strict":
                            item["NEW_stress_correlated_result"] is not None and
                            item["NEW_stress_correlated_result"]["arithmetic_strict_target_test_passed"]})
    negative = producer.old_controls.rejections(original, model, record["results"][0], radius_lower, arcs)
    scope_negative = []
    for label, mutation in (
        ("balanced-old-numerical-schema-laundered", lambda bad: bad.update(schema=producer.old.SCHEMA)),
        ("balanced-own-executor-spoofed", lambda bad: bad.update(executed_probe_sha256="0"*64)),
        ("balanced-old-source-forest-digest-substituted", lambda bad: bad.update(checked_v7_forest_sha256="0"*64)),
        ("balanced-other-whole-root-owner-imported", lambda bad: bad.update(source_OPEN_index=25)),
        ("balanced-proof-payment-invented", lambda bad: bad.update(verified=True, new_geometric_payments=1)),
        ("balanced-cover-counterexample-invented", lambda bad: bad.update(
            continuous_disk_cover_and_global_optimality_counterexample_NOT_proved=False)),
        ("balanced-old100000-objective-relabelled-as1", lambda bad:
            bad["results"][0]["numerical_minimax_and_equilibrium_suggestions_NOT_proofs"].update(numerical_objective_scale=100000)),
        ("balanced-hidden-duplicate-old-leaf-case", lambda bad: bad["results"].append(deepcopy(bad["results"][0]))),
    ):
        bad = deepcopy(record)
        mutation(bad)
        try:
            scope_gate(bad, seed, row, model, layer, old_record, args, digests)
        except (ValueError, KeyError, TypeError, IndexError):
            scope_negative.append(label)
        else:
            raise AssertionError("invalid actual balanced scope accepted: "+label)
    if len(negative) != 16 or len(scope_negative) != 8:
        raise AssertionError("balanced independent test omitted a required actual guard")
    producer.old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": digests[args.diagnosis],
        "actual_balanced_full134rod_point_and_stress_results_independently_reconstructed": checked,
        "independent_actual_all134rod_interval_distance_checks": len(checked)*134,
        "independent_actual_all60_free_unit_disk_checks": len(checked)*60,
        "fresh_NEW60ground_harmonic_Schur_and_nonharmonic_identities_checked": len(checked),
        "actual_point_radius_stress_rejection_controls_passed": negative,
        "actual_balanced_executor_source_scope_rejection_controls_passed": scope_negative,
        "old_reports_all_NONOPEN_proofs_and_NEWEST_running_histories_UNMODIFIED": True,
        "successful_v7_stress_supplement_NEEDS_fresh_actual_v8_OPEN_descendant_reconstruction": True,
        "continuous_disk_cover_and_global_optimality_counterexample_NOT_proved": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_balanced_probe_sha256": binding.sha(producer.__file__),
        "tested_independent_point_stress_module_sha256": binding.sha(producer.old_controls.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_balanced_full134rod_independent_controls_completed": True,
                      "actual_checked_v7_leaves": len(checked), "actual_rejections": len(negative)+len(scope_negative),
                      "below_Rstar_full134rod_relaxation_points": sum(
                          item["exact_below_Rstar_full134rod_NECESSARY_model_realization"] for item in checked),
                      "fresh_strict_balanced_stress_whole_leaves": sum(
                          item["fresh_balanced_stress_correlated_whole_leaf_strict"] for item in checked),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
