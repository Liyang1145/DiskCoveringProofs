"""Independent full prior962 retention and correct selected fresh-support append."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import compose_current538_failed_joint_physical as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-current538-checked-failed-joint-physical-support-append-v1"


def retention(record,args,seed,batch,strict):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_current_predecessor_file"] != linux(args.seed)
        or record["actual_current_predecessor_sha256"] != args.seed_sha256
        or record["actual_current_predecessor_controls_sha256"] != args.seed_controls_sha256
        or record["actual_checked_fresh_failed_joint_batch_sha256"] != args.batch_sha256
        or record["actual_checked_fresh_failed_joint_controls_sha256"] != args.batch_controls_sha256
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["new_whole_original_FAILED_leaf_indices"] != sorted(strict)
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("independent fresh failed-joint append changed source,parent,batch or scope")
    table,expected,offset = list(seed["full134rod_supports"]),{},19
    if (
        len(record["nodes"]) != 2999
        or any(record["nodes"][i] != node for i,node in enumerate(seed["nodes"]) if i not in strict)
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["fresh_joint_origin_supports"] != seed["fresh_joint_origin_supports"]
    ):
        raise ValueError("independent fresh failed-joint append reset old node/origin history")
    mixed = producer.batch_producer.source.MIXED
    for target in batch["actual_failed_whole_leaf_fresh_trials"]:
        leaf,proof = target["actual_current_failed_whole_OPEN_leaf"],target["selected_strict_physical_proof"]
        index = leaf["index"]
        if index not in strict:
            continue
        if seed["nodes"][index] != {"kind":"OPEN"} or index not in seed["retained_failed_CURRENT_whole_leaf_indices"]:
            raise ValueError("independent fresh append re-paid a nonFAILED/nonOPEN old leaf")
        table.append({"mode":mixed.SUPPORT_MODE,"kernel_certificate":proof["fresh_physical_kernel_certificate"],
                      "suggestion_point_turns":proof["joint_reference_turns"]})
        node = {"kind":mixed.KIND,"full_support_index":offset,"certificate":proof["certificate"]}
        if record["nodes"][index] != node:
            raise ValueError("independent fresh append changed whole physical proof or fresh index")
        expected[index] = {**leaf,"kind":mixed.KIND,"full_support_index":offset,
                           "certificate":proof["certificate"],"arithmetic_result":proof["arithmetic_result"]}
        offset += 1
    if record["full134rod_supports"] != table:
        raise ValueError("independent fresh append changed old19 prefix or selected fresh support list")
    old = {item["index"]:item for item in seed["arithmetic_ledger"]}
    new = {item["index"]:item for item in record["arithmetic_ledger"]}
    if (
        len(old) != 962 or len(new) != len(record["arithmetic_ledger"]) or len(new) != 962+len(strict)
        or set(new)-set(old) != strict
        or any(new.get(i) != item for i,item in old.items())
        or any(new.get(i) != item for i,item in expected.items())
    ):
        raise ValueError("independent fresh append lost an old962 row or a new whole failed-region proof")
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        record["pending_closed_leaf_boxes"] != pending or len(pending) != 538-len(strict)
        or record["remaining_OPEN_leaf_count"] != len(pending)
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 984-len(pending)
        or record["retained_old_failed_whole_leaf_indices"] != [
            i for i in seed["retained_failed_CURRENT_whole_leaf_indices"] if i not in strict]
    ):
        raise ValueError("independent fresh append omitted other unproved or failed whole domains")


def main():
    parser = argparse.ArgumentParser()
    producer.arguments(parser)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual exact fresh append and new independent output required")
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
            raise AssertionError("invalid fresh failed-joint append accepted: "+label)

    def gate(changed):
        return retention(changed,args,seed,batch,strict)

    reject("fresh-append-promoted-to-global",lambda:gate({**record,"global_optimality_proved":True}))
    reject("old962-strict-row-omitted",lambda:gate({**record,"arithmetic_ledger":record["arithmetic_ledger"][1:]}))
    reject("unpaid538-whole-domain-omitted",lambda:gate({
        **record,"pending_closed_leaf_boxes":record["pending_closed_leaf_boxes"][:-1]}))
    table = list(record["full134rod_supports"])
    table[0] = table[-1]
    reject("old19-support-prefix-replaced",lambda:gate({**record,"full134rod_supports":table}))
    nodes = list(record["nodes"])
    nodes[2641] = {"kind":"OPEN"}
    reject("old-complete2641-origin-forest-reset",lambda:gate({**record,"nodes":nodes}))
    if strict:
        index = min(strict)
        rows = list(record["arithmetic_ledger"])
        position = next(i for i,row in enumerate(rows) if row["index"] == index)
        target = deepcopy(rows[position])
        target["upper"][0] = target["lower"][0]
        rows[position] = target
        reject("proper-subbox-forged-as-entire-failed-domain",lambda:gate({**record,"arithmetic_ledger":rows}))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("fresh append source changed during independent retention checks")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh append diagnosis changed during independent checks")
    inventory.update(record["input_sha256"])
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_predecessor_sha256":args.seed_sha256,
        "actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "actual_checked_fresh_failed_joint_batch_sha256":args.batch_sha256,
        "actual_checked_fresh_failed_joint_controls_sha256":args.batch_controls_sha256,
        "new_whole_original_FAILED_leaf_indices":sorted(strict),
        "remaining_OPEN_leaf_count":538-len(strict),
        "total_whole_original_v4_OPEN_leaves_excluded":446+len(strict),
        "physical_full134_support_count":len(record["full134rod_supports"]),
        "all2999_old_domains_old19support_prefix962rows_and_origin_histories_retained":True,
        "all_selected_fresh_inverse_certificates_and_whole_domain_support_indices_bound":True,
        "retained_old_failed_whole_leaf_indices":record["retained_old_failed_whole_leaf_indices"],
        "arithmetic_history_composition_ONLY_NOT_geometry_cache":True,
        "prior_mathematics_explicit_qualified_REUSE_NOT_fresh_all_history_replay":True,
        "actual_scope_prefix_old_row_origin_history_and_subset_rejection_controls":rejected,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_fresh_failed_joint_append_completed_NOT_admission":True,
                      "new_whole_old_FAILED_exclusions":len(strict),"remaining_OPEN":538-len(strict),
                      "physical_supports":len(record["full134rod_supports"]),
                      "old19_prefix_and962rows_retained":True,"actual_rejection_controls":len(rejected)}),flush=True)


if __name__ == "__main__":
    main()
