"""Checked arithmetic join ONLY: paired918 plus independently checked fresh batch.

Old mathematics is honestly reused. This is not a source/geometry cache,
not whole-root acceptance and not a new replay of all old strict leaves.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest918_joint_stress_source as source
import probe_latest918_joint_origin_stress_batch as batch_producer
import test_latest918_joint_origin_stress_batch as batch_tester
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest-root25-checked-fresh-joint-origin-batch-composition-v1"
KIND = "FRESH-FULL134-TWO-ORIGIN-BRANCHES-ENERGY"
DIAGNOSIS = Path("outputs/n26-latest918-joint-origin-fresh-stress-batch-diagnostic-v1.json")
CONTROLS = Path("outputs/n26-latest918-joint-origin-fresh-stress-batch-independent-controls-v1.json")


def inputs(diagnosis_sha, controls_sha):
    if (
        binding.sha(source.SEED) != source.SEED_SHA or binding.sha(source.CONTROLS) != source.CONTROL_SHA
        or binding.sha(DIAGNOSIS) != diagnosis_sha or binding.sha(CONTROLS) != controls_sha
    ):
        raise ValueError("fresh arithmetic join needs the actual completed pair and latest918 seed")
    seed, seed_controls = binding.read(source.SEED), binding.read(source.CONTROLS)
    diagnosis, controls = binding.read(DIAGNOSIS), binding.read(CONTROLS)
    source.scope(seed, seed_controls)
    batch_tester.scope(diagnosis, seed)
    strict = source.target_gate(diagnosis, seed, seed["pending_closed_leaf_boxes"])
    if (
        controls["schema"] != batch_tester.SCHEMA or controls["diagnosis_sha256"] != diagnosis_sha
        or controls["actual_paired918_diagnosis_sha256"] != source.SEED_SHA
        or controls["actual_paired918_controls_sha256"] != source.CONTROL_SHA
        or controls["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or controls["source_file_sha256"] != seed["source_file_sha256"]
        or controls["actual_new_strict_whole_leaf_indices"] != sorted(strict)
        or controls["prospective_arithmetic_remaining_OPEN_after_independent_join"] != 918-len(strict)
        or controls["all2999_closed_domains_AND582_prior_strict_rows_independently_retained"] is not True
        or controls["all66_prior_whole_exclusions_AND2641_complete_origin_forest_retained"] is not True
        or controls["known_exact_covering_root_not_excluded_by_new_complete_origin_kernel_unions"] is not True
        or controls["executed_test_sha256"] != binding.sha(batch_tester.__file__)
        or controls["verified"] is not False or controls["new_geometric_payments"] != 0
        or any(controls[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("fresh arithmetic join changed independently checked two-owner whole-leaf scope")
    checked = {
        (item["whole_leaf_index"], item["origin_center_label"]): item
        for item in controls["all_actual_fresh_whole_origin_branch_bounds_including_failures_independently_recomputed"]
    }
    for index in strict:
        for owner in (16, 25):
            item = checked[index, owner]
            if item["strict_entire_branch"] is not True or F(item["strict_radius_margin"]) <= 0:
                raise ValueError("fresh arithmetic join lacks an independently strict entire owner branch")
    inventory = {}
    for record in (seed, seed_controls, diagnosis, controls):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("checked fresh arithmetic join prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("checked fresh arithmetic join prerequisite conflict")
            inventory[text] = digest
    inventory.update({
        linux(source.SEED): source.SEED_SHA, linux(source.CONTROLS): source.CONTROL_SHA,
        linux(DIAGNOSIS): diagnosis_sha, linux(CONTROLS): controls_sha,
        linux(__file__): binding.sha(__file__),
    })
    return seed, seed_controls, diagnosis, controls, strict, inventory


def compose(seed, diagnosis, strict, diagnosis_sha, controls_sha):
    nodes, ledger, supports = list(seed["nodes"]), list(seed["arithmetic_ledger"]), []
    for item in diagnosis["actual_joint_stress_whole_leaf_trials"]:
        leaf = item["actual_latest918_whole_OPEN_leaf"]
        index = leaf["index"]
        if index not in strict:
            continue
        proofs = []
        for trial in item["actual_origin_branch_trials"]:
            support_index = len(supports)
            supports.append({
                "origin_center_label": trial["origin_center_label"],
                "base_kernel_certificate": trial["fresh_positive134rod_kernel_certificate"],
                "origin_multiplier": trial["fresh_origin_multiplier"],
            })
            proofs.append({
                "origin_center_label": trial["origin_center_label"], "fresh_joint_support_index": support_index,
                "certificate": trial["whole_origin_branch_certificate"],
            })
        node = {"kind": KIND, "origin_branch_certificates": proofs}
        nodes[index] = node
        ledger.append({
            **leaf, "kind": KIND, "origin_branch_certificates": proofs,
            "complete_fresh_joint_batch_diagnosis_sha256": diagnosis_sha,
            "complete_fresh_joint_batch_independent_controls_sha256": controls_sha,
        })
    ledger.sort(key=lambda item: item["index"])
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        len(nodes) != 2999 or len(ledger) != 582+len(strict) or len(pending) != 918-len(strict)
        or any(nodes[index] != node for index, node in enumerate(seed["nodes"]) if node["kind"] != "OPEN")
        or nodes[2539] != seed["nodes"][2539] or nodes[2641] != seed["nodes"][2641]
    ):
        raise ValueError("fresh arithmetic join lost old nodes or complete branch/forest history")
    return nodes, ledger, pending, supports


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--batch-sha256", required=True)
    parser.add_argument("--controls-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve fresh arithmetic successor")
    seed, seed_controls, diagnosis, controls, strict, inventory = inputs(args.batch_sha256, args.controls_sha256)
    if not strict:
        raise ValueError("zero newly checked whole-leaf exclusions cannot advance the latest arithmetic head")
    nodes, ledger, pending, supports = compose(seed, diagnosis, strict, args.batch_sha256, args.controls_sha256)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("fresh arithmetic join source changed during composition")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_source_closed_box": seed["actual_source_closed_box"], "source_file_sha256": seed["source_file_sha256"],
        "actual_checked918_predecessor_sha256": source.SEED_SHA,
        "actual_checked918_controls_sha256": source.CONTROL_SHA,
        "actual_complete_fresh_joint_batch_diagnosis_sha256": args.batch_sha256,
        "actual_complete_fresh_joint_batch_controls_sha256": args.controls_sha256,
        "new_whole_actual918_OPEN_leaf_indices": sorted(strict),
        "nodes": nodes, "alternative_supports": seed["alternative_supports"],
        "full134rod_supports": seed["full134rod_supports"], "fresh_joint_origin_supports": supports,
        "arithmetic_ledger": ledger, "pending_closed_leaf_boxes": pending,
        "remaining_OPEN_leaf_count": len(pending),
        "total_whole_original_v4_OPEN_leaves_excluded": 66+len(strict),
        "all2999_domains_splits_old_supports_and582_prior_strict_rows_retained": True,
        "complete2539_two_origin_proof_AND2641_origin_forest_bindings_retained": True,
        "old_and_new_mathematics_qualified_checked_REUSE_NOT_full_replay": True,
        "this_is_only_arithmetic_history_composition_NOT_geometry_cache": True,
        "new_independent_global_arithmetic_retention_controls_STILL_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_producer_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "fresh_joint_checked_arithmetic_composition_completed_NOT_admission": True,
        "new_whole_leaf_exclusions": len(strict), "remaining_OPEN": len(pending),
        "old582_strict_rows_retained": True,
    }), flush=True)


if __name__ == "__main__":
    main()
