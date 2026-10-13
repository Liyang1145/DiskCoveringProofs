"""Checked shared-support arithmetic history join; not geometry admission."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest910_shared_origin_source as source
import test_latest910_shared_origin_support_sweep as tester
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest-root25-checked-shared-origin-support-sweep-composition-v1"
KIND = "SHARED-FRESH-FULL134-TWO-ORIGIN-BRANCHES-ENERGY"
BATCH = Path("outputs/n26-latest910-shared-fresh-origin-support-sweep-diagnostic-v1.json")
CONTROLS = Path("outputs/n26-latest910-shared-fresh-origin-support-sweep-independent-controls-v1.json")


def inputs(batch_sha, control_sha):
    if (
        binding.sha(source.SEED) != source.SEED_SHA or binding.sha(source.CONTROLS) != source.CONTROL_SHA
        or binding.sha(BATCH) != batch_sha or binding.sha(CONTROLS) != control_sha
    ):
        raise ValueError("shared arithmetic join changed actual paired910 or completed sweep pair")
    seed, old_controls = binding.read(source.SEED), binding.read(source.CONTROLS)
    batch, controls = binding.read(BATCH), binding.read(CONTROLS)
    source.scope(seed, old_controls)
    tester.scope(batch, seed)
    strict = source.target_gate(batch, seed, seed["pending_closed_leaf_boxes"])
    if (
        controls["schema"] != tester.SCHEMA or controls["diagnosis_sha256"] != batch_sha
        or controls["actual_paired910_diagnosis_sha256"] != source.SEED_SHA
        or controls["actual_paired910_controls_sha256"] != source.CONTROL_SHA
        or controls["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or controls["source_file_sha256"] != seed["source_file_sha256"]
        or controls["actual_new_strict_whole_leaf_indices"] != sorted(strict)
        or controls["prospective_arithmetic_remaining_OPEN_after_independent_join"] != 910-len(strict)
        or controls["all2999_closed_domains_and590_prior_strict_rows_and16_shared_supports_retained"] is not True
        or controls["all74_prior_whole_exclusions_and2641_complete_origin_forest_retained"] is not True
        or controls["known_exact_covering_root_not_excluded_by_any_new_complete_origin_kernel_union"] is not True
        or controls["executed_test_sha256"] != binding.sha(tester.__file__)
        or controls["verified"] is not False or controls["new_geometric_payments"] != 0
        or any(controls[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("shared arithmetic join lost actual independent full-domain/owner proof scope")
    checked = controls["all_actual_new_whole_origin_branch_bounds_including_failures_independently_recomputed"]
    by_key = {(item["whole_leaf_index"], item["origin_center_label"], item["shared_fresh_support_index"]): item
              for item in checked}
    for target in batch["actual_shared_fresh_whole_leaf_trials"]:
        index = target["actual_latest910_whole_OPEN_leaf"]["index"]
        if index not in strict:
            continue
        for proof in target["strict_origin_branch_proofs"]:
            item = by_key[index, proof["origin_center_label"], proof["shared_fresh_support_index"]]
            if item["strict_entire_branch"] is not True or F(item["strict_radius_margin"]) <= 0:
                raise ValueError("shared arithmetic join promoted an unchecked or nonstrict owner")
    inventory = {}
    for record in (seed, old_controls, batch, controls):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("shared arithmetic join checked prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("shared arithmetic join prerequisite identity conflict")
            inventory[text] = digest
    inventory.update({
        linux(source.SEED): source.SEED_SHA, linux(source.CONTROLS): source.CONTROL_SHA,
        linux(BATCH): batch_sha, linux(CONTROLS): control_sha, linux(__file__): binding.sha(__file__),
    })
    return seed, batch, controls, strict, inventory


def compose(seed, batch, strict, batch_sha, control_sha):
    nodes, ledger = list(seed["nodes"]), list(seed["arithmetic_ledger"])
    for item in batch["actual_shared_fresh_whole_leaf_trials"]:
        leaf = item["actual_latest910_whole_OPEN_leaf"]
        if leaf["index"] not in strict:
            continue
        branches = [{
            "origin_center_label": proof["origin_center_label"],
            "shared_fresh_support_index": proof["shared_fresh_support_index"],
            "certificate": proof["certificate"],
        } for proof in item["strict_origin_branch_proofs"]]
        nodes[leaf["index"]] = {"kind": KIND, "origin_branch_certificates": branches}
        ledger.append({
            **leaf, "kind": KIND, "origin_branch_certificates": branches,
            "checked_shared_sweep_diagnosis_sha256": batch_sha,
            "checked_shared_sweep_independent_controls_sha256": control_sha,
        })
    ledger.sort(key=lambda item: item["index"])
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    return nodes, ledger, pending


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--batch-sha256", required=True)
    parser.add_argument("--controls-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve completed shared arithmetic successor")
    seed, batch, controls, strict, inventory = inputs(args.batch_sha256, args.controls_sha256)
    if not strict:
        raise ValueError("zero newly checked whole-leaf exclusions cannot advance arithmetic history")
    nodes, ledger, pending = compose(seed, batch, strict, args.batch_sha256, args.controls_sha256)
    if (
        len(nodes) != 2999 or len(ledger) != 590+len(strict) or len(pending) != 910-len(strict)
        or any(nodes[index] != node for index, node in enumerate(seed["nodes"]) if node["kind"] != "OPEN")
    ):
        raise ValueError("shared arithmetic join changed old proof/split/domain history")
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("shared arithmetic source changed during composition")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_source_closed_box": seed["actual_source_closed_box"], "source_file_sha256": seed["source_file_sha256"],
        "actual_checked910_predecessor_sha256": source.SEED_SHA,
        "actual_checked910_controls_sha256": source.CONTROL_SHA,
        "actual_complete_shared_sweep_diagnosis_sha256": args.batch_sha256,
        "actual_complete_shared_sweep_controls_sha256": args.controls_sha256,
        "new_whole_actual910_OPEN_leaf_indices": sorted(strict),
        "nodes": nodes, "alternative_supports": seed["alternative_supports"],
        "full134rod_supports": seed["full134rod_supports"],
        "fresh_joint_origin_supports": seed["fresh_joint_origin_supports"],
        "arithmetic_ledger": ledger, "pending_closed_leaf_boxes": pending,
        "remaining_OPEN_leaf_count": len(pending),
        "total_whole_original_v4_OPEN_leaves_excluded": 74+len(strict),
        "all2999_domains_splits_old_supports16_fresh_supports_and590_prior_strict_rows_retained": True,
        "complete2539_two_origin_AND2641_origin_forest_ANDprevious8fresh_whole_leaves_retained": True,
        "old_AND_new_mathematics_explicit_qualified_checked_REUSE_NOT_full_replay": True,
        "this_is_only_arithmetic_history_composition_NOT_geometry_cache": True,
        "new_independent_global_arithmetic_retention_controls_STILL_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_producer_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "shared_fresh_checked_arithmetic_join_completed_NOT_admission": True,
        "new_whole_leaf_exclusions": len(strict), "remaining_OPEN": len(pending),
        "all590prior_strict_rows_and16shared_supports_retained": True,
    }), flush=True)


if __name__ == "__main__":
    main()
