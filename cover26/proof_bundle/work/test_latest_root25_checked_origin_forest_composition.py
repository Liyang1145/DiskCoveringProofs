"""Independent exact919->918 arithmetic history join, not repeated mathematics."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import compose_latest_root25_checked_origin_forest as producer
import test_checked_root28_full134rod_intersections as domains
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-latest-root25-checked-origin-forest-arithmetic-composition-v1"


def independent_retention(record,prior,branch,control):
    if (
        record["schema"] != producer.SCHEMA or record["verified"] is not False
        or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != prior["actual_source_closed_box"]
        or record["source_file_sha256"] != prior["source_file_sha256"]
        or record["new_entire_old_OPEN_leaf_excluded"] != 2641
        or record["new_geometric_payments"] != 0
        or record["global_optimality_proved"] is not False
        or record["actual_checked919_predecessor_sha256"] != producer.old.PRIOR_SHA
        or record["actual_checked919_controls_sha256"] != producer.old.PRIOR_CONTROL_SHA
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
    ):
        raise ValueError("independent arithmetic composition changed actual latest owner/unpaid scope")
    original = {item["index"]:item for item in prior["pending_closed_leaf_boxes"]}
    leaf = branch["actual_prior_whole_leaf"]
    if original.get(2641) != leaf or leaf != control["actual_prior_whole_leaf"]:
        raise ValueError("independent composition changed entire previous OPEN bounds")
    expected_node = {
        "kind":producer.KIND,"origin_center_labels":[16,25],
        "whole_origin16_checked_predecessor_sha256":producer.old.PRIOR_SHA,
        "whole_origin16_source_leaf_index":2641,
        "complete_origin25_forest_diagnosis_file":linux(producer.BRANCH),
        "complete_origin25_forest_diagnosis_sha256":record["actual_complete_origin25_forest_diagnosis_sha256"],
        "complete_origin25_forest_independent_controls_file":linux(producer.CONTROLS),
        "complete_origin25_forest_independent_controls_sha256":record["actual_complete_origin25_forest_controls_sha256"],
    }
    if (
        len(record["nodes"]) != len(prior["nodes"])
        or any(record["nodes"][index] != node for index,node in enumerate(prior["nodes"]) if index != 2641)
        or record["nodes"][2641] != expected_node
        or record["alternative_supports"] != prior["alternative_supports"]
        or record["full134rod_supports"] != prior["full134rod_supports"]
    ):
        raise ValueError("independent arithmetic composition reset another leaf/support/split")
    expected_pending = [item for item in prior["pending_closed_leaf_boxes"] if item["index"] != 2641]
    if record["pending_closed_leaf_boxes"] != expected_pending or len(expected_pending) != 918:
        raise ValueError("independent composition lost another unpaid source")
    old = {item["index"]:item for item in prior["arithmetic_ledger"]}
    new = {item["index"]:item for item in record["arithmetic_ledger"]}
    if (
        len(old) != 581 or len(new) != len(record["arithmetic_ledger"]) or len(new) != 582
        or any(new.get(index) != item for index,item in old.items())
        or set(new)-set(old) != {2641}
        or new[2641] != {**leaf,"kind":producer.KIND,"complete_two_origin_forest_proof_binding":expected_node}
        or record["remaining_OPEN_leaf_count"] != 918
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 66
    ):
        raise ValueError("independent composition lost a581-prior proof or clipped new entire leaf")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch-sha256",required=True)
    parser.add_argument("--controls-sha256",required=True)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh exact checked global arithmetic composition required")
    prior,branch,control,inventory = producer.inputs(args.branch_sha256,args.controls_sha256)
    record = binding.read(args.diagnosis)
    if (
        record["actual_complete_origin25_forest_diagnosis_sha256"] != args.branch_sha256
        or record["actual_complete_origin25_forest_controls_sha256"] != args.controls_sha256
        or record["nodes"][2641]["complete_origin25_forest_diagnosis_sha256"] != args.branch_sha256
        or record["nodes"][2641]["complete_origin25_forest_independent_controls_sha256"] != args.controls_sha256
    ):
        raise ValueError("independent composition bound another branch pair")
    independent_retention(record,prior,branch,control)
    # Full domain walk only; prior arithmetic is qualified checked reuse.
    source = producer.old
    original,model,bases,old_prior,old_control,leaf,whole16,arcs,model_inventory = source.inputs()
    before,before_parents = domains.all_domains(original,prior["actual_source_closed_box"],prior["nodes"])
    after,after_parents = domains.all_domains(original,record["actual_source_closed_box"],record["nodes"])
    if before != after or before_parents != after_parents:
        raise ValueError("independent composition changed a closed domain/shared split endpoint")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid latest arithmetic composition accepted: "+label)
    changed = {**record,"global_optimality_proved":True}
    reject("arithmetic-join-promoted-to-global-optimality",lambda:independent_retention(changed,prior,branch,control))
    changed = deepcopy(record)
    changed["pending_closed_leaf_boxes"].pop()
    reject("unpaid-whole-root-leaf-omitted",lambda:independent_retention(changed,prior,branch,control))
    changed = deepcopy(record)
    changed["arithmetic_ledger"].pop(0)
    reject("old581-strict-row-omitted",lambda:independent_retention(changed,prior,branch,control))
    changed = deepcopy(record)
    changed["nodes"][2539] = {"kind":"OPEN"}
    reject("previous-complete-two-origin-proof-reset",lambda:independent_retention(changed,prior,branch,control))
    changed = deepcopy(record)
    changed["nodes"][2641]["origin_center_labels"] = [25]
    reject("one-branch-forged-as-two-origin-entire-leaf",lambda:independent_retention(changed,prior,branch,control))
    changed = deepcopy(record)
    new = next(item for item in changed["arithmetic_ledger"] if item["index"] == 2641)
    new["lower"][0] = new["upper"][0]
    reject("proper-subbox-forged-as-old-whole-leaf",lambda:independent_retention(changed,prior,branch,control))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("checked global arithmetic composition input changed during independent check")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("checked global arithmetic composition changed during independent check")
    inventory.update(model_inventory)
    inventory.update(record["input_sha256"])
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__),
                      linux(domains.__file__):binding.sha(domains.__file__)})
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_checked919_predecessor_sha256":producer.old.PRIOR_SHA,
        "actual_complete_origin25_forest_diagnosis_sha256":args.branch_sha256,
        "actual_complete_origin25_forest_controls_sha256":args.controls_sha256,
        "all2999_actual_closed_domains_splits_supports_AND581_old_strict_rows_independently_retained":True,
        "actual_new_entire_old_OPEN_leaf_excluded":2641,"remaining_OPEN_leaf_count":918,
        "total_whole_original_v4_OPEN_leaves_excluded":66,
        "arithmetic_only_qualified_prior_proof_composition_NOT_a_new_geometry_cache":True,
        "no_claim_of_fresh_all_old_or_branch_mathematics_replay":True,
        "actual_owner_retention_subset_and_scope_rejection_controls":rejected,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_latest_checked_arithmetic_two_origin_join_completed_NOT_admission":True,
                      "remaining_OPEN":918,"old581_strict_rows_retained":True,
                      "actual_rejection_controls":len(rejected),"formal_geometric_payments":0}),flush=True)


if __name__ == "__main__":
    main()
