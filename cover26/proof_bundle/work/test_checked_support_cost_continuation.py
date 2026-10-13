"""Independent actual v7/v8 arithmetic, history retention and new splits."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_support_cost_forest as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-checked-support-cost-continuation-controls-v1"


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "seed-controls",
                 "policy-controls", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, kernel, seed, controls, row, arcs, digests = producer.data_gate(args)
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    previous = producer.previous
    if (record["schema"] != producer.SCHEMA
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or record["old_arithmetic_forest_sha256"] != digests[args.seed]
            or record["actual_seed_independent_arithmetic_controls_sha256"] != digests[args.seed_controls]
            or record["actual_split_policy_controls_sha256"] != digests[args.policy_controls]
            or record["source_file_sha256"] != seed["source_file_sha256"]
            or record["all_previous_proved_closed_leaf_ledgers_preserved_identically"] is not True):
        raise ValueError("actual checked continuation changed newest independent lineage")
    previous.old_controls.previous.scope_gate(record, row)
    for module in (producer.forest, producer.forest.prior, producer.forest.prior.signed,
                   producer.support_step, previous, previous.producer,
                   previous.policy_controls, producer.codec, producer.identity):
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("actual checked continuation imported arithmetic changed")
    retained_nodes, retained_supports, retained_leaves = previous.old_controls.previous.retention_gate(
        seed, record)
    previous.old_controls.previous.reconstruct(original, kernel, arcs, row, seed, "v7-checked-seed")
    result, pending, ledger = previous.old_controls.previous.reconstruct(
        original, kernel, arcs, row, record, "v8-checked-support-cost-continuation")
    energy, local, empty = previous.old_controls.leaf_controls(original, kernel, arcs, record)
    rejected = previous.old_controls.previous.rejection_controls(
        original, kernel, arcs, row, seed, record)
    splits, narrow = previous.split_decision_gate(original, row, seed, record)
    if len(rejected) != 20:
        raise AssertionError("checked continuation omitted a required actual arithmetic rejection")
    for path, expected in {**digests, args.diagnosis: digest}.items():
        if binding.sha(path) != expected:
            raise ValueError("actual checked continuation input changed during independent controls")
    for name, expected in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != expected:
            raise ValueError("actual source/history DATA changed during independent controls")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": row["index"],
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "diagnosis_sha256": digest, "seed_sha256": digests[args.seed],
        "seed_controls_sha256": digests[args.seed_controls],
        "policy_controls_sha256": digests[args.policy_controls],
        "both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed": True,
        "all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically": True,
        "old_nodes_retained": retained_nodes, "old_positive_supports_retained": retained_supports,
        "old_proved_closed_leaves_retained": retained_leaves,
        "latest_arithmetic_result": result,
        "actual_strict_energy_leaves_independently_checked": energy,
        "independent_sine_square_feasible_corner_midpoint_checks": energy*3,
        "actual_original_LOCAL_leaves_reconstructed_not_declared_empty": local,
        "actual_exact_EMPTY_leaves_reconstructed": empty,
        "actual_rejection_controls_passed": rejected,
        "independently_tested_actual_split_policy_rejections":
            controls["independently_tested_actual_split_policy_rejections"],
        "actual_new_closed_splits_and_shared_boundaries_reconstructed": splits,
        "new_actual_root_tight_coordinate_splits_checked": narrow,
        "retained_OPEN_leaves": len(pending), "entire_root_arithmetic_cover_completed": not pending,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in (producer, producer.forest, producer.forest.prior,
                                          producer.forest.prior.signed, producer.support_step,
                                          previous, previous.producer, previous.policy_controls,
                                          producer.codec, producer.identity)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_checked_support_cost_continuation_controls_completed": True,
                      "strict_energy_leaves": energy, "original_LOCAL_leaves": local,
                      "OPEN_leaves": len(pending), "new_closed_splits": splits,
                      "actual_rejections": len(rejected),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
