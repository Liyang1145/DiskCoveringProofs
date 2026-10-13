"""Independent complete current node,row,prefix and two-owner append retention."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import compose_current_missing_origin_refit_v1 as producer
import verify_conditional_force_stage as binding


source = producer.source
SCHEMA = source.APPEND_CONTROL


def retention(record,args,seed,batch,strict):
    source.unpaid(record)
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_current_predecessor_file"] != linux(args.seed)
        or record["actual_current_predecessor_sha256"] != args.seed_sha256
        or record["actual_current_predecessor_controls_file"] != linux(args.seed_controls)
        or record["actual_current_predecessor_controls_sha256"] != args.seed_controls_sha256
        or record["actual_checked_current_origin_admission_file"] != linux(args.batch)
        or record["actual_checked_current_origin_admission_sha256"] != args.batch_sha256
        or record["actual_checked_current_origin_controls_file"] != linux(args.batch_controls)
        or record["actual_checked_current_origin_controls_sha256"] != args.batch_controls_sha256
        or record["parameter_pilot_sha256"] != args.pilot_sha256
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["new_whole_actual_current_leaf_indices"] != sorted(strict)
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["honest_distinct_append_schema_NOT_unchanged_table_reuse"] is not True
    ):
        raise ValueError("independent origin append changed actual source,parent,role or scope")
    if (
        len(record["nodes"]) != 2999 or len(record["nodes"]) != len(seed["nodes"])
        or any(record["nodes"][i] != node for i,node in enumerate(seed["nodes"]) if i not in strict)
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["fresh_joint_origin_supports"] != seed["fresh_joint_origin_supports"]
    ):
        raise ValueError("independent origin append reset a node or historical origin/support table")
    table,expected = list(seed["full134rod_supports"]),{}
    for target in batch["actual_current_two_owner_whole_trials"]:
        leaf = target["actual_current_whole_OPEN_leaf"]
        index = leaf["index"]
        if index not in strict:
            continue
        if seed["nodes"][index] != {"kind":"OPEN"}:
            raise ValueError("independent origin append re-paid a previously accepted whole domain")
        branches,rows = [],[]
        for proof in target["actual_whole_origin_branch_proofs"]:
            if "fresh_physical_base_kernel_certificate" in proof:
                support = len(table)
                table.append({"mode":source.MIXED.SUPPORT_MODE,
                              "kernel_certificate":proof["fresh_physical_base_kernel_certificate"],
                              "suggestion_point_turns":proof["fresh_base_reference_turns"]})
            else:
                support = proof["base_full_support_index"]
            branch = {"origin_center_label":proof["origin_center_label"],"base_full_support_index":support,
                      "origin_multiplier":proof["origin_multiplier"],"certificate":proof["certificate"]}
            branches.append(branch)
            rows.append({**branch,"arithmetic_result":proof["arithmetic_result"]})
        if len(branches) != 2 or {proof["origin_center_label"] for proof in branches} != {16,25} or record["nodes"][index] != {
                "kind":source.KIND,"origin_branch_certificates":branches}:
            raise ValueError("independent origin append omitted or changed an actual entire owner")
        expected[index] = {**leaf,"kind":source.KIND,"origin_branch_proofs":rows}
    if (
        record["full134rod_supports"] != table
        or len(table) != args.expected_supports+len(strict) or len(table) > source.MIXED.MAX_FULL_SUPPORTS
        or record["actual_current_support_count"] != len(table)
    ):
        raise ValueError("independent origin append replaced the full old prefix or duplicated a new base")
    old = {leaf["index"]:leaf for leaf in seed["arithmetic_ledger"]}
    new = {leaf["index"]:leaf for leaf in record["arithmetic_ledger"]}
    if (
        len(new) != len(record["arithmetic_ledger"]) or len(new) != len(old)+len(strict)
        or set(new)-set(old) != strict or any(new.get(i) != leaf for i,leaf in old.items())
        or any(new.get(i) != leaf for i,leaf in expected.items())
    ):
        raise ValueError("independent origin append lost an old row or changed a whole-current proof")
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        record["pending_closed_leaf_boxes"] != pending or len(pending) != args.expected_open-len(strict)
        or record["remaining_OPEN_leaf_count"] != len(pending)
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 984-len(pending)
        or record["retained_old_current_nodes_supports_and_rows"] != [
            len(seed["nodes"]),len(seed["alternative_supports"]),len(seed["arithmetic_ledger"])]
    ):
        raise ValueError("independent origin append lost unselected/failed domains or old accounting")


def main():
    parser = argparse.ArgumentParser()
    producer.arguments(parser)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed current origin append and fresh independent retention required")
    seed,batch,controls,strict,inventory = producer.inputs(args)
    record = binding.read(args.diagnosis)
    retention(record,args,seed,batch,strict)
    rejected = []
    def reject(label,changed):
        try:
            retention(changed,args,seed,batch,strict)
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid current origin append accepted: "+label)
    reject("arithmetic-promoted-to-global",{**record,"global_optimality_proved":True})
    reject("old-row-lost",{**record,"arithmetic_ledger":record["arithmetic_ledger"][1:]})
    reject("failed-or-unselected-domain-omitted",{**record,"pending_closed_leaf_boxes":record["pending_closed_leaf_boxes"][:-1]})
    table = list(record["full134rod_supports"])
    table[0] = table[-1]
    reject("old27-support-prefix-replaced",{**record,"full134rod_supports":table})
    nodes = list(record["nodes"])
    nodes[2641] = {"kind":"OPEN"}
    reject("old-complete-origin-forest-reset",{**record,"nodes":nodes})
    if strict:
        index = min(strict)
        nodes = list(record["nodes"])
        changed = deepcopy(nodes[index])
        changed["origin_branch_certificates"] = changed["origin_branch_certificates"][:1]
        nodes[index] = changed
        reject("entire-new-owner-omitted",{**record,"nodes":nodes})
        rows = list(record["arithmetic_ledger"])
        position = next(i for i,leaf in enumerate(rows) if leaf["index"] == index)
        changed = deepcopy(rows[position])
        axis = next(i for i,(a,b) in enumerate(zip(changed["lower"],changed["upper"])) if a != b)
        changed["upper"][axis] = changed["lower"][axis]
        rows[position] = changed
        reject("proper-subbox-forged-entire-current-domain",{**record,"arithmetic_ledger":rows})
    inventory.update(record["input_sha256"])
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    source.inventory_gate(inventory)
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_predecessor_sha256":args.seed_sha256,"actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "new_whole_actual_current_leaf_indices":sorted(strict),
        "remaining_OPEN_leaf_count":args.expected_open-len(strict),
        "total_whole_original_v4_OPEN_leaves_excluded":984-args.expected_open+len(strict),
        "actual_current_support_count":args.expected_supports+len(strict),
        "all_old_current_nodes_supports_and_strict_rows_retained":True,
        "all_old_physical_prefix_and_origin_donors_unchanged_only_selected_new_bases_appended":True,
        "BOTH_whole_actual_origin_branches_checked_before_each_new_payment":True,
        "all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained":True,
        "old_ANDnew_math_qualified_checked_REUSE_NOT_all_history_replay":True,
        "latest_geometry_and_unrestricted_global_acceptance_STILL_required":True,
        "actual_scope_source_owner_domain_prefix_history_and_retention_rejections":rejected,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_current_origin_append_complete_NOT_geometry":True,"new_whole_exclusions":len(strict),
                      "remaining_OPEN":args.expected_open-len(strict),
                      "actual_physical_support_count":args.expected_supports+len(strict),
                      "actual_rejections":len(rejected)}),flush=True)


if __name__ == "__main__":
    main()
