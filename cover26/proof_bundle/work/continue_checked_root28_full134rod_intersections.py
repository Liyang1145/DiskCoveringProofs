"""Actual checked v8 -> preserved mixed full134rod intersection arithmetic.

Refuses the old v7 fixture as its latest seed. No geometry admission and no
payments; latest v8 producer AND its automatic independent controls are
required before any continuation can begin.
"""

import argparse
from argparse import Namespace
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_checked_full134rod_closed_intersections as intersections
import probe_balanced_full134rod_neighborhoods as ancestor_inputs
import test_balanced_full134rod_neighborhoods as ancestor_controls
import test_checked_support_cost_continuation as latest_controls
import test_mixed_full134rod_support_forest as mode_controls
import test_preserved_closed_subbox_partition as partition_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-checked-v8-preserved-full134rod-intersection-forest-v1"
mixed = intersections.mixed
PATH_ARGUMENTS = (
    "resource", "resource-replay", "current-audit", "ancestor-current-audit",
    "source", "seed", "seed-controls", "policy-controls", "ancestor-seed",
    "old-full-diagnosis", "old-full-controls", "prior-diagnosis", "prior-controls",
    "correlated-diagnosis", "correlated-controls", "old-minimax-diagnosis",
    "old-minimax-controls", "balanced-diagnosis", "balanced-controls",
    "neighborhood-diagnosis", "neighborhood-controls", "mode-controls",
    "partition-controls", "latest-forest", "latest-controls",
)


def arguments(test=False):
    parser = argparse.ArgumentParser()
    for name in (*PATH_ARGUMENTS, *(("diagnosis",) if test else ()), "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    if not test:
        parser.add_argument("--max-targets", type=int, default=64)
    return parser.parse_args()


def modules():
    previous = latest_controls.producer.previous
    return (
        intersections, intersections.cutter, mixed, mixed.correlated,
        mixed.correlated.full, mixed.old, mixed.old.prior, mixed.old.prior.signed,
        latest_controls, latest_controls.producer,
        latest_controls.producer.support_step, previous, previous.producer,
        previous.policy_controls, latest_controls.producer.codec,
        latest_controls.producer.identity, ancestor_inputs, ancestor_controls,
        mode_controls, partition_controls,
    )


def argument_digests(args):
    paths = []
    for name in PATH_ARGUMENTS:
        path = getattr(args, name.replace("-", "_"))
        # Bundle arguments name directories; bind their real acceptance
        # bytes, not a filesystem directory masquerading as a file digest.
        if name in ("resource", "source"):
            path = path / "VERIFIED.json"
        paths.append(path)
    return {path: binding.sha(path) for path in paths}


def latest_gate(latest, controls, seed, args, digests):
    producer = latest_controls.producer
    if (latest["schema"] != producer.SCHEMA
            or latest["executed_producer_sha256"] != binding.sha(producer.__file__)
            or latest["old_arithmetic_forest_sha256"] != digests[args.seed]
            or latest["actual_seed_independent_arithmetic_controls_sha256"] != digests[args.seed_controls]
            or latest["actual_split_policy_controls_sha256"] != digests[args.policy_controls]
            or latest["source_file_sha256"] != seed["source_file_sha256"]
            or controls["schema"] != latest_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(latest_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.latest_forest]
            or controls["seed_sha256"] != digests[args.seed]
            or controls["seed_controls_sha256"] != digests[args.seed_controls]
            or controls["policy_controls_sha256"] != digests[args.policy_controls]
            or controls["source_file_sha256"] != seed["source_file_sha256"]
            or controls["latest_arithmetic_result"] != latest["arithmetic_result"]
            or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
            or controls["all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically"] is not True
            or len(controls["actual_rejection_controls_passed"]) != 20
            or len(controls["independently_tested_actual_split_policy_rejections"]) != 8
            or controls["independent_sine_square_feasible_corner_midpoint_checks"] !=
            3*controls["actual_strict_energy_leaves_independently_checked"]
            or latest["source_OPEN_index"] != 28 or controls["source_OPEN_index"] != 28):
        raise ValueError("mixed continuation lacks the actual completed checked latest v8 and controls")
    for record in (latest, controls):
        if (record["verified"] is not False or record["new_geometric_payments"] != 0
                or record["candidate_whole_roots_removed"] != 0
                or record["global_lower_bound_proved"] is not False
                or record["global_optimality_proved"] is not False):
            raise ValueError("latest arithmetic forest was promoted to geometry")
    previous = producer.previous
    previous.old_controls.previous.retention_gate(seed, latest)
    for module in (
        producer.forest, producer.forest.prior, producer.forest.prior.signed,
        producer.support_step, previous, previous.producer,
        previous.policy_controls, producer.codec, producer.identity,
    ):
        digest = binding.sha(module.__file__)
        if (latest["modules"][linux(Path(module.__file__))] != digest
                or controls["tested_modules"][Path(module.__file__).name] != digest):
            raise ValueError("checked latest v8 arithmetic changed after actual controls")


def data_gate(args):
    # Old v7 reports are evidence for stresses/regions ONLY, never the newest
    # continuation seed. Retain their proof-time audit identity explicitly.
    old_args = Namespace(**vars(args))
    old_args.current_audit = args.ancestor_current_audit
    original, model, seed, row, arcs, digests, _, stresses = ancestor_inputs.data_gate(old_args)
    digests.update(argument_digests(args))
    latest, controls = binding.read(args.latest_forest), binding.read(args.latest_controls)
    latest_gate(latest, controls, seed, args, digests)
    previous = latest_controls.producer.previous
    previous.old_controls.previous.scope_gate(latest, row)
    original_kernel = latest_controls.producer.codec.gate(
        binding.read(args.resource / "CONTEXT.json")["typed_context"])["original_kernel"]
    result, pending, ledger = previous.old_controls.previous.reconstruct(
        original, original_kernel, arcs, row, latest, "actual-latest-v8-before-NEW134rod")
    if result != controls["latest_arithmetic_result"] or pending != latest["pending_closed_leaf_boxes"]:
        raise ValueError("mixed continuation failed actual latest whole-forest reconstruction")
    current, current_digest = binding.read(args.current_audit), digests[args.current_audit]
    layer = latest_controls.producer.identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("mixed continuation changed the actual same-root radius")
    diagnosis = binding.read(args.neighborhood_diagnosis)
    neighborhood_test = binding.read(args.neighborhood_controls)
    ancestor_controls.payment_scope_gate(diagnosis)
    if (diagnosis["schema"] != ancestor_inputs.SCHEMA
            or diagnosis["executed_probe_sha256"] != binding.sha(ancestor_inputs.__file__)
            or diagnosis["checked_v7_forest_sha256"] != digests[args.seed]
            or diagnosis["source_file_sha256"] != seed["source_file_sha256"]
            or neighborhood_test["schema"] != ancestor_controls.SCHEMA
            or neighborhood_test["executed_test_sha256"] != binding.sha(ancestor_controls.__file__)
            or neighborhood_test["diagnosis_sha256"] != digests[args.neighborhood_diagnosis]
            or len(neighborhood_test["actual_closed_subset_and_no_payment_rejection_controls_passed"]) != 8
            or neighborhood_test["verified"] is not False
            or neighborhood_test["new_geometric_payments"] != 0):
        raise ValueError("mixed continuation changed actual proper-region evidence")
    mode, partition = binding.read(args.mode_controls), binding.read(args.partition_controls)
    if (mode["schema"] != mode_controls.SCHEMA
            or mode["executed_test_sha256"] != binding.sha(mode_controls.__file__)
            or mode["tested_mixed_forest_module_sha256"] != binding.sha(mixed.__file__)
            or mode["old_v7_nodes_checked"] != len(seed["nodes"])
            or mode["old_v7_strict_ledgers_checked"] != len(seed["arithmetic_ledger"])
            or len(mode["actual_mixed_mode_rejection_controls_passed"]) != 25
            or partition["schema"] != partition_controls.SCHEMA
            or partition["executed_test_sha256"] != binding.sha(partition_controls.__file__)
            or partition["seed_OLD_v7_sha256"] != digests[args.seed]
            or partition["tested_closed_subbox_module_sha256"] != binding.sha(intersections.cutter.__file__)
            or partition["tested_mixed_forest_module_sha256"] != binding.sha(mixed.__file__)
            or len(partition["actual_preserved_subbox_rejection_controls_passed"]) != 10):
        raise ValueError("mixed continuation changed tested distinct mode or closed-cut mechanisms")
    for fixture in (mode, partition):
        if (fixture["source_file_sha256"] != seed["source_file_sha256"]
                or fixture["verified"] is not False or fixture["new_geometric_payments"] != 0
                or fixture["candidate_whole_roots_removed"] != 0):
            raise ValueError("old arithmetic fixture was promoted to a newest geometric payment")
    table = [{
        "mode": mixed.SUPPORT_MODE,
        "kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
        "suggestion_point_turns": item["actual_fixed_feasible_anchor_turns"],
    } for item in stresses["results"]]
    kernels = mixed.full_support_gate(model, table)
    source_cases = {item["actual_checked_v7_OPEN_leaf"]["index"]: (index, item)
                    for index, item in enumerate(stresses["results"])}
    regions, seen = [], set()
    for item in diagnosis["results"]:
        ancestor_index = item["actual_checked_v7_OPEN_leaf"]["index"]
        support_index, old_item = source_cases[ancestor_index]
        if (ancestor_index in seen or item["actual_checked_v7_OPEN_leaf"] != old_item["actual_checked_v7_OPEN_leaf"]
                or item["NEW_full134rod_stress_kernel_certificate"] != table[support_index]["kernel_certificate"]):
            raise ValueError("mixed continuation changed a checked ancestor region/kernel")
        seen.add(ancestor_index)
        trial = next(trial for trial in item["trials"] if trial["requested_closed_half_width"] == "1/1000")
        target = ancestor_controls.neighborhood_gate(original, old_item, trial)
        certificate = trial["NEW_stress_correlated_certificate"]
        fresh = mixed.correlated.bound(
            kernels[support_index], original["matrix"], target["lower"], target["upper"],
            certificate, original["radius"], arcs)
        if (fresh != trial["NEW_stress_correlated_result"]
                or fresh["arithmetic_strict_target_test_passed"] is not True):
            raise ValueError("mixed continuation region lacks fresh exact strict arithmetic")
        regions.append({**target, "full_support_index": support_index,
                        "certificate": deepcopy(certificate)})
    if seen != set(source_cases) or not regions:
        raise ValueError("mixed continuation omitted a checked ancestor neighborhood")
    return original, original_kernel, latest, row, arcs, digests, layer, table, kernels, regions


def unchanged_inputs(args, digests, latest, module_digests, executed_digest):
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("mixed continuation input changed during execution")
    for name, digest in latest["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("mixed continuation actual source/history DATA changed")
    for path, digest in module_digests.items():
        if binding.sha(binding.local_path(path)) != digest:
            raise ValueError("mixed continuation arithmetic module changed during execution")
    if binding.sha(__file__) != executed_digest:
        raise ValueError("mixed continuation producer changed during execution")


def main():
    args = arguments()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, original_kernel, latest, row, arcs, digests, layer, table, kernels, regions = data_gate(args)
    executed_digest = binding.sha(__file__)
    module_digests = {linux(Path(module.__file__)): binding.sha(module.__file__) for module in modules()}

    def progress(target, count):
        print(json.dumps({
            "fresh_strict_targets": count,
            "actual_latest_OPEN_source": target["source_actual_OPEN_leaf"]["index"],
            "whole_actual_source_OPEN_leaf": target["whole_source_OPEN_leaf"],
            "verified": False, "new_geometric_payments": 0,
        }), flush=True)

    nodes, targets, decisions, scans = intersections.refine(
        original, arcs, row, latest["nodes"], kernels, regions, args.max_targets, progress)
    result, pending, ledger = mixed.replay(
        original, original_kernel, arcs, row, nodes, latest["alternative_supports"], table)
    retained = mixed.retention_gate(latest, {
        "nodes": nodes, "alternative_supports": latest["alternative_supports"],
        "full134rod_supports": table, "arithmetic_ledger": ledger,
    })
    unchanged_inputs(args, digests, latest, module_digests, executed_digest)
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": row["index"],
        "actual_source_closed_box": row, "source_file_sha256": latest["source_file_sha256"],
        "actual_current_audit_sha256": digests[args.current_audit],
        "actual_latest_candidate_layer_identity_only": layer,
        "actual_checked_latest_v8_forest_sha256": digests[args.latest_forest],
        "actual_checked_latest_v8_controls_sha256": digests[args.latest_controls],
        "ancestor_v7_is_region_evidence_ONLY_not_the_continuation_seed": True,
        "all_input_sha256": {linux(path): digest for path, digest in digests.items()},
        "old_latest_nodes_supports_and_strict_ledgers_retained": list(retained),
        "nodes": nodes, "alternative_supports": latest["alternative_supports"],
        "full134rod_supports": table, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "checked_proper_ancestor_regions_DATA_only": regions,
        "fresh_actual_latest_OPEN_intersection_targets": targets,
        "fresh_closed_split_decisions": decisions, "region_scans": scans,
        "max_fresh_strict_targets": args.max_targets,
        "all_old_nonOPEN_nodes_and_original_LOCAL_preserved": True,
        "both_closed_halves_shared_boundaries_and_all_remainders_retained": True,
        "latest_arithmetic_successor_independent_controls_still_required": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "modules": module_digests,
        "executed_producer_sha256": executed_digest,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_checked_v8_preserved_full134rod_intersections_completed": True,
        "fresh_strict_targets": len(targets), "fresh_closed_splits": len(decisions),
        "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
