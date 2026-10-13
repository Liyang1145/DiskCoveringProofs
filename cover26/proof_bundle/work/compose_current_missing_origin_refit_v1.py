"""Honest current physical support append with two-owner origin certificates."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import admit_current_missing_origin_refit_parameters_v1 as admission
import test_current_missing_origin_refit_admission_v1 as tester
import verify_conditional_force_stage as binding


source = admission.source
SCHEMA = source.APPEND_SCHEMA


def arguments(parser):
    admission.arguments(parser)
    parser.add_argument("--batch",type=Path,required=True)
    parser.add_argument("--batch-sha256",required=True)
    parser.add_argument("--batch-controls",type=Path,required=True)
    parser.add_argument("--batch-controls-sha256",required=True)


def inputs(args):
    seed,old_controls,inventory = source.paired(args)
    if binding.sha(args.batch) != args.batch_sha256 or binding.sha(args.batch_controls) != args.batch_controls_sha256:
        raise ValueError("actual completed current two-owner admission/control pair required")
    batch,controls = binding.read(args.batch),binding.read(args.batch_controls)
    admission.scope(batch,args,seed)
    strict = admission.ownership(batch,seed,seed["pending_closed_leaf_boxes"])
    source.unpaid(controls)
    if (
        controls["schema"] != tester.SCHEMA or controls["diagnosis_sha256"] != args.batch_sha256
        or controls["actual_current_seed_sha256"] != args.seed_sha256
        or controls["actual_current_controls_sha256"] != args.seed_controls_sha256
        or controls["actual_current_OPEN_count"] != args.expected_open
        or controls["actual_current_physical_support_count"] != args.expected_supports
        or controls["parameter_pilot_sha256"] != args.pilot_sha256
        or controls["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or controls["source_file_sha256"] != seed["source_file_sha256"]
        or controls["new_whole_actual_current_leaf_indices"] != sorted(strict)
        or controls["selected_NEW_physical_bases_independently_checked"] != len(strict)
        or controls["BOTH_whole_actual_origin_branches_checked_before_each_new_payment"] is not True
        or controls["all_old_current_nodes_tables_and_rows_UNMODIFIED"] is not True
        or controls["known_exact_root_not_falsely_excluded_by_each_complete_origin_union"] is not True
        or controls["executed_test_sha256"] != binding.sha(tester.__file__)
    ):
        raise ValueError("current origin append lost actual independent source,owner or budget controls")
    checks = controls["all_actual_current_owner_bounds_independently_recomputed"]
    seen = {(item["whole_leaf_index"],item["origin_center_label"]) for item in checks}
    if len(seen) != len(checks) or seen != {(index,owner) for index in strict for owner in (16,25)}:
        raise ValueError("current origin append omitted or duplicated a whole-owner independent check")
    if any(item["strict_whole_origin_branch"] is not True or F(item["strict_radius_margin"]) <= 0 for item in checks):
        raise ValueError("current origin append promoted an unchecked/nonstrict owner")
    for record in (batch,controls):
        source.inventory_gate(record["input_sha256"])
        for text,digest in record["input_sha256"].items():
            if text in inventory and inventory[text] != digest:
                raise ValueError("current origin append prerequisite conflict")
            inventory[text] = digest
    inventory.update({linux(args.batch):args.batch_sha256,linux(args.batch_controls):args.batch_controls_sha256,
                      linux(__file__):binding.sha(__file__)})
    return seed,batch,controls,strict,inventory


def compose(seed,batch,strict):
    nodes,ledger,table = list(seed["nodes"]),list(seed["arithmetic_ledger"]),list(seed["full134rod_supports"])
    for target in batch["actual_current_two_owner_whole_trials"]:
        leaf = target["actual_current_whole_OPEN_leaf"]
        if leaf["index"] not in strict:
            continue
        proofs,rows = [],[]
        for proof in target["actual_whole_origin_branch_proofs"]:
            if "fresh_physical_base_kernel_certificate" in proof:
                support = len(table)
                table.append({"mode":source.MIXED.SUPPORT_MODE,
                              "kernel_certificate":proof["fresh_physical_base_kernel_certificate"],
                              "suggestion_point_turns":proof["fresh_base_reference_turns"]})
            else:
                support = proof["base_full_support_index"]
                if type(support) is not int or not 0 <= support < len(seed["full134rod_supports"]):
                    raise ValueError("current retained owner substituted a nonexistent old physical base")
            descriptor = {"origin_center_label":proof["origin_center_label"],"base_full_support_index":support,
                          "origin_multiplier":proof["origin_multiplier"],"certificate":proof["certificate"]}
            proofs.append(descriptor)
            rows.append({**descriptor,"arithmetic_result":proof["arithmetic_result"]})
        nodes[leaf["index"]] = {"kind":source.KIND,"origin_branch_certificates":proofs}
        ledger.append({**leaf,"kind":source.KIND,"origin_branch_proofs":rows})
    ledger.sort(key=lambda leaf:leaf["index"])
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if len(table) > source.MIXED.MAX_FULL_SUPPORTS or len(table) != len(seed["full134rod_supports"])+len(strict):
        raise ValueError("current origin append duplicated bases or exceeded the real support limit64")
    return nodes,ledger,pending,table


def main():
    parser = argparse.ArgumentParser()
    arguments(parser)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve completed current origin append")
    seed,batch,controls,strict,inventory = inputs(args)
    if not strict:
        raise ValueError("zero new whole-owner exclusions do not advance current history")
    nodes,ledger,pending,table = compose(seed,batch,strict)
    payload = {"nodes":nodes,"arithmetic_ledger":ledger,"alternative_supports":seed["alternative_supports"],
               "full134rod_supports":table}
    retained = source.MIXED.retention_gate(seed,payload)
    source.inventory_gate(inventory)
    record = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_source_closed_box":seed["actual_source_closed_box"],"source_file_sha256":seed["source_file_sha256"],
        "actual_current_predecessor_file":linux(args.seed),"actual_current_predecessor_sha256":args.seed_sha256,
        "actual_current_predecessor_controls_file":linux(args.seed_controls),
        "actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "actual_checked_current_origin_admission_file":linux(args.batch),
        "actual_checked_current_origin_admission_sha256":args.batch_sha256,
        "actual_checked_current_origin_controls_file":linux(args.batch_controls),
        "actual_checked_current_origin_controls_sha256":args.batch_controls_sha256,
        "parameter_pilot_sha256":args.pilot_sha256,"new_whole_actual_current_leaf_indices":sorted(strict),
        **payload,"fresh_joint_origin_supports":seed["fresh_joint_origin_supports"],
        "pending_closed_leaf_boxes":pending,"remaining_OPEN_leaf_count":len(pending),
        "total_whole_original_v4_OPEN_leaves_excluded":984-len(pending),"actual_current_support_count":len(table),
        "retained_old_current_nodes_supports_and_rows":list(retained),
        "all_old_physical_prefix_and_origin_donors_unchanged_only_selected_new_bases_appended":True,
        "BOTH_whole_actual_origin_branches_checked_before_each_new_payment":True,
        "all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained":True,
        "old_ANDnew_mathematics_qualified_checked_REUSE_NOT_fresh_all_history_replay":True,
        "honest_distinct_append_schema_NOT_unchanged_table_reuse":True,
        "latest_source_geometry_current_admission_and_independent_retention_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(record,indent=2)+"\n")
    print(json.dumps({"actual_current_two_owner_append_complete_NOT_geometry":True,"new_whole_exclusions":len(strict),
                      "remaining_OPEN":len(pending),"actual_physical_support_count":len(table)}),flush=True)


if __name__ == "__main__":
    main()
