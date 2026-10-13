"""Checked physical-support append on actual FAILED538 domains; retain old19."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_current538_failed_joint_physical_stresses as batch_producer
import test_current538_failed_joint_physical_stresses as batch_tester
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current538-checked-failed-joint-physical-support-append-v1"


def arguments(parser):
    batch_producer.source.arguments(parser)
    parser.add_argument("--batch",type=Path,required=True)
    parser.add_argument("--batch-sha256",required=True)
    parser.add_argument("--batch-controls",type=Path,required=True)
    parser.add_argument("--batch-controls-sha256",required=True)


def inputs(args):
    seed,old_controls,inventory = batch_producer.source.paired(args)
    if args.expected_open != 538 or binding.sha(args.batch) != args.batch_sha256 or binding.sha(args.batch_controls) != args.batch_controls_sha256:
        raise ValueError("fresh failed-joint join changed actual538 or completed batch pair")
    batch,controls = binding.read(args.batch),binding.read(args.batch_controls)
    batch_tester.scope(batch,args,seed)
    strict = batch_producer.ownership(batch,seed,seed["pending_closed_leaf_boxes"])
    if (
        controls["schema"] != batch_tester.SCHEMA or controls["diagnosis_sha256"] != args.batch_sha256
        or controls["actual_current_seed_sha256"] != args.seed_sha256
        or controls["actual_current_controls_sha256"] != args.seed_controls_sha256
        or controls["new_strict_whole_leaf_indices"] != sorted(strict)
        or controls["prospective_remaining_OPEN_after_independent_join"] != 538-len(strict)
        or controls["all_original_failed44_sources_and_current538_domains_independently_retained"] is not True
        or controls["all962_old_strict_rows19supports_and_old_histories_UNMODIFIED"] is not True
        or controls["no_actual_origin_requirement_or_virtual_budget_in_new_PHYSICAL_proofs"] is not True
        or controls["known_exact_covering_root_not_falsely_excluded_by_fresh_kernels"] is not True
        or controls["executed_test_sha256"] != binding.sha(batch_tester.__file__)
        or controls["verified"] is not False or controls["new_geometric_payments"] != 0
        or any(controls[field] is not False for field in
               ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("fresh failed-joint join lost independent physical/failure-source scope")
    checked = controls["all_actual_fresh_physical_inverse_and_whole_bounds_including_failures_independently_checked"]
    for index in strict:
        if not any(item["whole_leaf_index"] == index and item.get("strict_whole_leaf") is True
                   and F(item["strict_radius_margin"]) > 0 for item in checked):
            raise ValueError("fresh failed-joint target has no independent strict whole physical proof")
    for record in (batch,controls):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("fresh failed-joint join prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("fresh failed-joint join prerequisite conflict")
            inventory[text] = digest
    inventory.update({linux(args.batch):args.batch_sha256,linux(args.batch_controls):args.batch_controls_sha256,
                      linux(__file__):binding.sha(__file__)})
    return seed,batch,controls,strict,inventory


def compose(seed,batch,strict):
    mixed = batch_producer.source.MIXED
    nodes,ledger,table = list(seed["nodes"]),list(seed["arithmetic_ledger"]),list(seed["full134rod_supports"])
    for target in batch["actual_failed_whole_leaf_fresh_trials"]:
        leaf,proof = target["actual_current_failed_whole_OPEN_leaf"],target["selected_strict_physical_proof"]
        index = leaf["index"]
        if index not in strict:
            continue
        support = len(table)
        table.append({"mode":mixed.SUPPORT_MODE,"kernel_certificate":proof["fresh_physical_kernel_certificate"],
                      "suggestion_point_turns":proof["joint_reference_turns"]})
        nodes[index] = {"kind":mixed.KIND,"full_support_index":support,"certificate":proof["certificate"]}
        ledger.append({**leaf,"kind":mixed.KIND,"full_support_index":support,
                       "certificate":proof["certificate"],"arithmetic_result":proof["arithmetic_result"]})
    if len(table) > mixed.MAX_FULL_SUPPORTS:
        raise ValueError("new fresh failed-joint physical table exceeds real limit64")
    ledger.sort(key=lambda item:item["index"])
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    return nodes,ledger,pending,table


def main():
    parser = argparse.ArgumentParser()
    arguments(parser)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve actual fresh failed-joint successor")
    seed,batch,controls,strict,inventory = inputs(args)
    if not strict:
        raise ValueError("zero newly checked failed-region exclusions cannot advance current history")
    nodes,ledger,pending,table = compose(seed,batch,strict)
    arithmetic = {"nodes":nodes,"arithmetic_ledger":ledger,"alternative_supports":seed["alternative_supports"],
                  "full134rod_supports":table}
    retained = batch_producer.source.MIXED.retention_gate(seed,arithmetic)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("fresh failed-joint source changed during composition")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_source_closed_box":seed["actual_source_closed_box"],"source_file_sha256":seed["source_file_sha256"],
        "actual_current_predecessor_file":linux(args.seed),"actual_current_predecessor_sha256":args.seed_sha256,
        "actual_current_predecessor_controls_file":linux(args.seed_controls),
        "actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "actual_checked_fresh_failed_joint_batch_file":linux(args.batch),
        "actual_checked_fresh_failed_joint_batch_sha256":args.batch_sha256,
        "actual_checked_fresh_failed_joint_controls_file":linux(args.batch_controls),
        "actual_checked_fresh_failed_joint_controls_sha256":args.batch_controls_sha256,
        "new_whole_original_FAILED_leaf_indices":sorted(strict),**arithmetic,
        "fresh_joint_origin_supports":seed["fresh_joint_origin_supports"],
        "pending_closed_leaf_boxes":pending,"remaining_OPEN_leaf_count":len(pending),
        "total_whole_original_v4_OPEN_leaves_excluded":984-len(pending),
        "retained_old_current_nodes_supports_and962_strict_rows":list(retained),
        "old19_physical_support_prefix_UNCHANGED_new_selected_kernels_only_appended":True,
        "all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained":True,
        "retained_old_failed_whole_leaf_indices":[i for i in seed["retained_failed_CURRENT_whole_leaf_indices"] if i not in strict],
        "old_ANDnew_mathematics_explicit_qualified_checked_REUSE_NOT_full_replay":True,
        "arithmetic_history_composition_ONLY_NOT_geometry_cache":True,
        "new_independent_arithmetic_retention_controls_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"fresh_failed_joint_checked_arithmetic_join_completed_NOT_admission":True,
                      "new_whole_old_FAILED_exclusions":len(strict),"remaining_OPEN":len(pending),
                      "physical_supports":len(table),"old19_prefix_and962rows_retained":True}),flush=True)


if __name__ == "__main__":
    main()
