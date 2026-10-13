"""Distinct actual-v8 continuation using freshly checked grown root regions.

No old executor is patched or relabelled. Requires actual completed latest
v8 plus its automatic controls; all old proof modes and ledgers are retained.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_root28_full134rod_intersections as ancestor_interface
import n26_grown_full134rod_region_selection as selection
import probe_root_clipped_grown_full134rod_regions as region_producer
import test_root_clipped_grown_full134rod_regions as region_controls
import test_grown_full134rod_region_selection as selection_controls
import test_checked_root28_full134rod_intersections as independent_domains
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-checked-v8-grown-source-root-full134rod-intersection-forest-v1"
EXTRA_ARGUMENTS = (
    "grown-diagnosis", "grown-controls", "grown-selection-controls", "grown-current-audit",
)
mixed = ancestor_interface.mixed
NARROW_SUCCESSOR = Path(
    "outputs/n26-candidate-root28-preserved-full134rod-intersection-forest-diagnosis-v9.json")
NARROW_CONTROLS = Path(
    "outputs/n26-candidate-root28-preserved-full134rod-intersection-independent-controls-v1.json")


def arguments(test=False):
    parser = argparse.ArgumentParser()
    for name in (*ancestor_interface.PATH_ARGUMENTS, *EXTRA_ARGUMENTS,
                 *(("diagnosis",) if test else ()), "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    if not test:
        parser.add_argument("--max-targets", type=int, default=64)
    return parser.parse_args()


def no_latest_history_reset():
    if NARROW_SUCCESSOR.exists() or NARROW_CONTROLS.exists():
        raise ValueError("a narrow v9 history exists; do not reset it to v8 for a grown successor")


def modules():
    return (
        *ancestor_interface.modules(), ancestor_interface, selection,
        region_producer, region_controls, selection_controls, independent_domains,
        independent_domains.independent_energy,
    )


def grown_evidence_gate(record, controls, selected_controls, latest, row, layer,
                        proof_time_layer, args, digests):
    if (record["schema"] != region_producer.SCHEMA
            or record["executed_probe_sha256"] != binding.sha(region_producer.__file__)
            or record["actual_source_closed_box"] != row
            or record["source_OPEN_index"] != row["index"]
            or record["source_file_sha256"] != latest["source_file_sha256"]
            or record["explicit_OLD_v7_stress_origin_forest_sha256"] != digests[args.seed]
            or record["balanced_stress_diagnosis_sha256"] != digests[args.balanced_diagnosis]
            or record["balanced_stress_controls_sha256"] != digests[args.balanced_controls]
            or record["actual_supplied_current_audit_sha256"] != digests[args.grown_current_audit]
            or record["actual_latest_candidate_layer_identity_only"] != proof_time_layer
            or controls["schema"] != region_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(region_controls.__file__)
            or controls["tested_probe_sha256"] != binding.sha(region_producer.__file__)
            or controls["tested_independent_correlated_energy_sha256"] !=
            binding.sha(independent_domains.independent_energy.__file__)
            or controls["diagnosis_sha256"] != digests[args.grown_diagnosis]
            or controls["source_file_sha256"] != latest["source_file_sha256"]
            or len(controls["actual_root_subset_source_history_and_zero_payment_guards_rejected"]) != 10
            or selected_controls["schema"] != "N26-independent-pure-grown-full134rod-region-selection-controls-v1"
            or selected_controls["executed_test_sha256"] != binding.sha(selection_controls.__file__)
            or selected_controls["tested_pure_selection_module_sha256"] != binding.sha(selection.__file__)
            or selected_controls["diagnosis_sha256"] != digests[args.grown_diagnosis]
            or selected_controls["actual_grown_region_controls_sha256"] != digests[args.grown_controls]
            or len(selected_controls["actual_selection_scope_bound_and_false_strictness_controls_rejected"]) != 8):
        raise ValueError("grown successor lacks actual bound whole-region and pure-selection controls")
    for item in (record, controls, selected_controls):
        if (item["verified"] is not False or item["new_geometric_payments"] != 0
                or item["candidate_whole_roots_removed"] != 0
                or item["global_lower_bound_proved"] is not False
                or item["global_optimality_proved"] is not False):
            raise ValueError("grown arithmetic evidence was promoted to geometry")
    if (proof_time_layer["actual_latest_candidate_acceptance_sha256"] !=
            layer["actual_latest_candidate_acceptance_sha256"]
            or proof_time_layer["actual_latest_candidate_pending_angles_sha256"] !=
            layer["actual_latest_candidate_pending_angles_sha256"]):
        raise ValueError("grown proof-time model DATA reset the actual latest candidate source")
    for module in region_producer.modules():
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("grown whole-region arithmetic changed after independent testing")


def data_gate(args):
    no_latest_history_reset()
    # This shared interface freshly reconstructs actual v8, every old proof
    # ledger, current source identity, and the separately named old fixtures.
    values = ancestor_interface.data_gate(args)
    original, original_kernel, latest, row, arcs, digests, layer, table, kernels, _ = values
    for name in EXTRA_ARGUMENTS:
        path = getattr(args, name.replace("-", "_"))
        digests[path] = binding.sha(path)
    record, controls, selected_controls = (
        binding.read(args.grown_diagnosis), binding.read(args.grown_controls),
        binding.read(args.grown_selection_controls),
    )
    proof_time_layer = ancestor_interface.latest_controls.producer.identity.gate(
        binding.read(args.grown_current_audit), digests[args.grown_current_audit], args.source)
    grown_evidence_gate(
        record, controls, selected_controls, latest, row, layer,
        proof_time_layer, args, digests)
    regions, selection_audit = selection.select(original, arcs, row, table, record)
    if (regions != selected_controls["actual_selected_widest_strict_closed_regions"]
            or selection_audit != selected_controls["all_root_clipped_region_results_freshly_reconstructed"]
            or not regions):
        raise ValueError("grown successor failed fresh actual widest-strict-region reconstruction")
    evidence = {
        "grown_diagnosis_sha256": digests[args.grown_diagnosis],
        "grown_independent_controls_sha256": digests[args.grown_controls],
        "grown_pure_selection_controls_sha256": digests[args.grown_selection_controls],
        "separately_named_grown_proof_time_current_sha256": digests[args.grown_current_audit],
        "separately_named_grown_proof_time_candidate_identity_DATA_only": proof_time_layer,
        "all_grown_region_selection_results_freshly_reconstructed": selection_audit,
    }
    return original, original_kernel, latest, row, arcs, digests, layer, table, kernels, regions, evidence


def unchanged_inputs(args, digests, latest, module_digests, executed_digest):
    no_latest_history_reset()
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("grown successor input changed during execution")
    for name, digest in latest["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("grown successor actual source/model/history DATA changed")
    for path, digest in module_digests.items():
        if binding.sha(binding.local_path(path)) != digest:
            raise ValueError("grown successor executed arithmetic changed")
    if binding.sha(__file__) != executed_digest:
        raise ValueError("grown successor own producer changed during execution")


def main():
    args = arguments()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, kernel, latest, row, arcs, digests, layer, table, kernels, regions, evidence = data_gate(args)
    executed_digest = binding.sha(__file__)
    module_digests = {linux(Path(module.__file__)): binding.sha(module.__file__) for module in modules()}

    def progress(target, count):
        print(json.dumps({
            "grown_regions_fresh_strict_targets": count,
            "actual_latest_OPEN_source": target["source_actual_OPEN_leaf"]["index"],
            "whole_actual_latest_OPEN_leaf": target["whole_source_OPEN_leaf"],
            "verified": False, "new_geometric_payments": 0,
        }), flush=True)

    nodes, targets, decisions, scans = ancestor_interface.intersections.refine(
        original, arcs, row, latest["nodes"], kernels, regions, args.max_targets, progress)
    result, pending, ledger = mixed.replay(
        original, kernel, arcs, row, nodes, latest["alternative_supports"], table)
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
        "old_stress_origins_are_region_DATA_ONLY_not_the_latest_forest_seed": True,
        "narrow_unexecuted_interface_NOT_relabelled_as_this_distinct_own_producer": True,
        "grown_region_evidence_and_fresh_selection": evidence,
        "all_input_sha256": {linux(path): digest for path, digest in digests.items()},
        "old_latest_nodes_supports_and_strict_ledgers_retained": list(retained),
        "nodes": nodes, "alternative_supports": latest["alternative_supports"],
        "full134rod_supports": table, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "checked_grown_source_root_regions_DATA_only": regions,
        "fresh_actual_latest_OPEN_intersection_targets": targets,
        "fresh_closed_split_decisions": decisions, "region_scans": scans,
        "max_fresh_strict_targets": args.max_targets,
        "all_old_nonOPEN_nodes_original_LOCAL_support_prefixes_and_ledgers_preserved": True,
        "both_closed_halves_shared_boundaries_and_all_remainders_retained": True,
        "actual_successor_independent_arithmetic_controls_still_required": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_producer_sha256": executed_digest, "modules": module_digests,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_checked_v8_grown_full134rod_successor_completed": True,
        "fresh_strict_targets": len(targets), "fresh_closed_splits": len(decisions),
        "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
