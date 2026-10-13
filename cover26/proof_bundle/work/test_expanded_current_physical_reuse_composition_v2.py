"""Independent complete node/ledger/history retention for the expanded-table join."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import compose_expanded_current_physical_support_reuse_v2 as producer
import verify_conditional_force_stage as binding


SCHEMA = producer.source.REUSE_CONTROL


def retention(record,args,seed,batch,strict):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_current_predecessor_file"] != linux(args.seed)
        or record["actual_current_predecessor_sha256"] != args.seed_sha256
        or record["actual_current_predecessor_controls_file"] != linux(args.seed_controls)
        or record["actual_current_predecessor_controls_sha256"] != args.seed_controls_sha256
        or record["actual_complete_physical_reuse_batch_file"] != linux(args.batch)
        or record["actual_complete_physical_reuse_batch_sha256"] != args.batch_sha256
        or record["actual_complete_physical_reuse_controls_file"] != linux(args.batch_controls)
        or record["actual_complete_physical_reuse_controls_sha256"] != args.batch_controls_sha256
        or record["new_whole_actual_current_OPEN_leaf_indices"] != sorted(strict)
        or record["actual_current_support_count"] != args.expected_supports
        or record["expanded_actual_physical_support_table_reused_unchanged_NO_append"] is not True
        or record["all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained"] is not True
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("expanded independent join changed actual source,parent,batch,table or unpaid scope")
    if (
        len(record["nodes"]) != 2999 or len(record["nodes"]) != len(seed["nodes"])
        or any(record["nodes"][i] != node for i,node in enumerate(seed["nodes"]) if i not in strict)
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["full134rod_supports"] != seed["full134rod_supports"]
        or record["fresh_joint_origin_supports"] != seed["fresh_joint_origin_supports"]
    ):
        raise ValueError("expanded independent join reset a node/history or changed/appended supports")
    expected = {}
    for target in batch["actual_current_whole_leaf_trials"]:
        leaf,proof = target["actual_current_whole_OPEN_leaf"],target["selected_strict_physical_proof"]
        index = leaf["index"]
        if index not in strict:
            continue
        if seed["nodes"][index] != {"kind":"OPEN"}:
            raise ValueError("expanded independent join re-paid an old completed leaf")
        node = {"kind":producer.source.MIXED.KIND,
                "full_support_index":proof["full_support_index"],"certificate":proof["certificate"]}
        if record["nodes"][index] != node:
            raise ValueError("expanded independent join changed an actual entire-domain physical proof")
        expected[index] = {**leaf,"kind":producer.source.MIXED.KIND,
                           "full_support_index":proof["full_support_index"],"certificate":proof["certificate"],
                           "arithmetic_result":proof["arithmetic_result"]}
    old = {leaf["index"]:leaf for leaf in seed["arithmetic_ledger"]}
    new = {leaf["index"]:leaf for leaf in record["arithmetic_ledger"]}
    if (
        len(old) != len(seed["arithmetic_ledger"]) or len(new) != len(record["arithmetic_ledger"])
        or len(new) != len(old)+len(strict) or set(new)-set(old) != strict
        or any(new.get(i) != leaf for i,leaf in old.items())
        or any(new.get(i) != leaf for i,leaf in expected.items())
        or record["arithmetic_ledger"] != sorted(record["arithmetic_ledger"],key=lambda leaf:leaf["index"])
    ):
        raise ValueError("expanded independent join lost an old row or new entire-domain exact proof")
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        record["pending_closed_leaf_boxes"] != pending or len(pending) != args.expected_open-len(strict)
        or record["remaining_OPEN_leaf_count"] != len(pending)
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 984-len(pending)
        or record["retained_failed_CURRENT_whole_leaf_indices"] != batch["actual_failed_whole_leaf_indices"]
        or record["actual_attempt_method_parameters"] != batch["method_parameters"]
        or any(i not in {leaf["index"] for leaf in pending} for i in batch["actual_failed_whole_leaf_indices"])
    ):
        raise ValueError("expanded independent join omitted failed/unselected whole domains")
    if record["retained_old_current_nodes_supports_and_strict_rows"] != [
            len(seed["nodes"]),len(seed["alternative_supports"]),len(seed["arithmetic_ledger"])]:
        raise ValueError("expanded join misstated actual complete predecessor retention")


def main():
    parser = argparse.ArgumentParser()
    producer.arguments(parser)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed expanded join and fresh independent output required")
    seed,batch,controls,strict,inventory = producer.inputs(args)
    record = binding.read(args.diagnosis)
    retention(record,args,seed,batch,strict)
    rejected = []

    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid expanded physical join accepted: "+label)

    def gate(changed):
        return retention(changed,args,seed,batch,strict)

    reject("arithmetic-join-promoted-to-global",lambda:gate({**record,"global_optimality_proved":True}))
    reject("old-current-strict-row-lost",lambda:gate({**record,"arithmetic_ledger":record["arithmetic_ledger"][1:]}))
    if record["pending_closed_leaf_boxes"]:
        reject("unpaid-current-whole-domain-omitted",lambda:gate({
            **record,"pending_closed_leaf_boxes":record["pending_closed_leaf_boxes"][:-1]}))
    reject("same-expanded-support-appended-again",lambda:gate({
        **record,"full134rod_supports":[*record["full134rod_supports"],record["full134rod_supports"][-1]]}))
    reject("expanded-table-truncated-to-old19",lambda:gate({
        **record,"full134rod_supports":record["full134rod_supports"][:19]}))
    nodes = list(record["nodes"])
    nodes[2641] = {"kind":"OPEN"}
    reject("complete2641-origin-forest-reset",lambda:gate({**record,"nodes":nodes}))
    if strict:
        index = min(strict)
        nodes = list(record["nodes"])
        nodes[index] = {**nodes[index],"full_support_index":-1}
        reject("expanded-support-owner-forged",lambda:gate({**record,"nodes":nodes}))
        rows = list(record["arithmetic_ledger"])
        position = next(i for i,leaf in enumerate(rows) if leaf["index"] == index)
        leaf = deepcopy(rows[position])
        coordinate = next(i for i,(a,b) in enumerate(zip(leaf["lower"],leaf["upper"])) if a != b)
        leaf["upper"][coordinate] = leaf["lower"][coordinate]
        rows[position] = leaf
        reject("proper-subbox-forged-as-whole-current-domain",lambda:gate({**record,"arithmetic_ledger":rows}))
    for text,digest in {**inventory,**record["input_sha256"]}.items():
        if binding.sha(text) != digest:
            raise ValueError("expanded join prerequisite changed during independent retention")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("expanded join changed during independent retention")
    inventory.update(record["input_sha256"])
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_predecessor_file":linux(args.seed),"actual_current_predecessor_sha256":args.seed_sha256,
        "actual_current_predecessor_controls_file":linux(args.seed_controls),
        "actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "actual_complete_physical_reuse_batch_file":linux(args.batch),
        "actual_complete_physical_reuse_batch_sha256":args.batch_sha256,
        "actual_complete_physical_reuse_controls_file":linux(args.batch_controls),
        "actual_complete_physical_reuse_controls_sha256":args.batch_controls_sha256,
        "new_whole_actual_current_OPEN_leaf_indices":sorted(strict),
        "remaining_OPEN_leaf_count":args.expected_open-len(strict),
        "total_whole_original_v4_OPEN_leaves_excluded":984-args.expected_open+len(strict),
        "actual_current_support_count":args.expected_supports,
        "all_old_current_nodes_supports_and_strict_rows_retained":True,
        "expanded_actual_physical_support_table_reused_unchanged_NO_append":True,
        "all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained":True,
        "retained_failed_CURRENT_whole_leaf_indices":batch["actual_failed_whole_leaf_indices"],
        "arithmetic_only_checked_history_composition_NOT_geometry_cache":True,
        "prior_domain_ANDenergy_mathematics_explicit_qualified_REUSE_NOT_fresh_replay":True,
        "actual_scope_retention_table_history_owner_and_whole_subset_rejections":rejected,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_expanded_physical_join_completed_NOT_admission":True,
                      "new_whole_leaf_exclusions":len(strict),"remaining_OPEN":args.expected_open-len(strict),
                      "all_old_current_strict_rows_retained":True,
                      "actual_physical_supports_unchanged":args.expected_supports,
                      "actual_rejection_controls":len(rejected)}),flush=True)


if __name__ == "__main__":
    main()
