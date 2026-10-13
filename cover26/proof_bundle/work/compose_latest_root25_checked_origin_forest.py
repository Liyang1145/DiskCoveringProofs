"""Distinct ARITHMETIC history join: checked919 + complete leaf2641 branches.

Does not rerun old mathematics or act as latest geometry/source gate. Prior
checked pairs and immutable retention are explicit; current/globalflagsfalse.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_latest_origin_branch_closed_forest as old
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest-root25-checked-two-origin-closed-forest-composition-v1"
KIND = "FULL134-TWO-ORIGIN-CLOSED-FORESTS-ENERGY"
BRANCH = Path("outputs/n26-latest-origin25-joint-fresh-stress-successor-diagnostic-v1.json")
CONTROLS = Path("outputs/n26-latest-origin25-joint-fresh-stress-successor-independent-controls-v1.json")


def inputs(branch_sha,control_sha):
    if binding.sha(BRANCH) != branch_sha or binding.sha(CONTROLS) != control_sha:
        raise ValueError("latest arithmetic composition requires exact completed whole-origin branch pair")
    if binding.sha(old.PRIOR) != old.PRIOR_SHA or binding.sha(old.PRIOR_CONTROL) != old.PRIOR_CONTROL_SHA:
        raise ValueError("latest arithmetic composition reset its actual919 predecessor")
    prior,prior_control,branch,control = [binding.read(path) for path in (old.PRIOR,old.PRIOR_CONTROL,BRANCH,CONTROLS)]
    if (
        prior_control["diagnosis_sha256"] != old.PRIOR_SHA
        or prior_control["remaining_OPEN_leaf_count"] != 919 or prior["remaining_OPEN_leaf_count"] != 919
        or branch["schema"] != "N26-unaccepted-latest-origin25-joint-reference-fresh-stress-successor-v1"
        or control["schema"] != "N26-independent-joint-reference-origin25-fresh-stress-successor-controls-v1"
        or control["diagnosis_sha256"] != branch_sha
        or branch["actual_latest919_global_predecessor_sha256"] != old.PRIOR_SHA
        or control["actual_latest919_global_predecessor_sha256"] != old.PRIOR_SHA
        or branch["entire_origin25_branch_strictly_excluded"] is not True
        or control["entire_origin25_branch_strictly_excluded"] is not True
        or branch["both_checked_origin_branches_arithmetically_exclude_whole_leaf2641"] is not True
        or control["both_checked_origin_branches_arithmetically_exclude_whole_leaf2641"] is not True
        or branch["retained_origin25_OPEN_subleaves"] or control["retained_origin25_OPEN_subleaves"]
        or len(control["all_NEW_strict_entire_origin25_subleaf_bounds_independently_recomputed"]) != 2
        or control["all_old15_domains_and6prior_strict_rows_preserved_independently"] is not True
        or any(item["verified"] is not False or item["new_geometric_payments"] != 0
               or item["global_optimality_proved"] is not False
               for item in (prior,prior_control,branch,control))
    ):
        raise ValueError("latest arithmetic composition changed checked predecessor/complete two-branch scope")
    if (
        branch["executed_producer_sha256"] != binding.sha("work/probe_joint_fresh_origin25_stress_successor.py")
        or control["executed_test_sha256"] != binding.sha("work/test_joint_fresh_origin25_stress_successor.py")
    ):
        raise ValueError("actual completed branch producer/independent executable changed")
    inventory = {}
    for report in (prior,prior_control,branch,control):
        for text,digest in report["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("checked arithmetic composition input changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("checked arithmetic predecessor identity conflict")
            inventory[text] = digest
    inventory.update({
        linux(old.PRIOR):old.PRIOR_SHA,linux(old.PRIOR_CONTROL):old.PRIOR_CONTROL_SHA,
        linux(BRANCH):branch_sha,linux(CONTROLS):control_sha,linux(__file__):binding.sha(__file__),
    })
    return prior,branch,control,inventory


def compose(prior,branch,control,branch_sha,control_sha):
    leaf = branch["actual_prior_whole_leaf"]
    if leaf != control["actual_prior_whole_leaf"] or leaf["index"] != 2641:
        raise ValueError("complete checked two-origin forest belongs to another old leaf")
    by_index = {item["index"]:item for item in prior["pending_closed_leaf_boxes"]}
    if by_index.get(2641) != leaf or prior["nodes"][2641] != {"kind":"OPEN"}:
        raise ValueError("composition attempted a paid or clipped actual919 whole source leaf")
    whole16 = branch["whole_origin16_branch_prior_checked_proof"]
    original_item = next(item for item in prior["all_actual_leaf_origin_branch_trials"]
                         if item["actual_prior_OPEN_leaf"]["index"] == 2641)
    if (
        whole16 not in original_item["strict_origin_branch_proofs"]
        or whole16["origin_center_label"] != 16
        or whole16["arithmetic_result"]["arithmetic_strict_entire_origin_branch"] is not True
        or F(whole16["arithmetic_result"]["strict_energy_margin"]) <= 0
        or F(whole16["arithmetic_result"]["strict_radius_margin"]) <= 0
    ):
        raise ValueError("composition lost actual checked WHOLE first origin branch")
    nodes = deepcopy(prior["nodes"])
    node = {
        "kind":KIND,"origin_center_labels":[16,25],
        "whole_origin16_checked_predecessor_sha256":old.PRIOR_SHA,
        "whole_origin16_source_leaf_index":2641,
        "complete_origin25_forest_diagnosis_file":linux(BRANCH),
        "complete_origin25_forest_diagnosis_sha256":branch_sha,
        "complete_origin25_forest_independent_controls_file":linux(CONTROLS),
        "complete_origin25_forest_independent_controls_sha256":control_sha,
    }
    nodes[2641] = node
    ledger = deepcopy(prior["arithmetic_ledger"])
    ledger.append({**leaf,"kind":KIND,"complete_two_origin_forest_proof_binding":node})
    ledger.sort(key=lambda item:item["index"])
    pending = [item for item in prior["pending_closed_leaf_boxes"] if item["index"] != 2641]
    if (
        len(pending) != 918 or len(nodes) != 2999 or len(ledger) != 582
        or any(old_node["kind"] != "OPEN" and nodes[index] != old_node
               for index,old_node in enumerate(prior["nodes"]))
    ):
        raise ValueError("composition lost existing closed-domain/root history")
    return nodes,ledger,pending


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch-sha256",required=True)
    parser.add_argument("--controls-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve latest arithmetic composition")
    prior,branch,control,inventory = inputs(args.branch_sha256,args.controls_sha256)
    nodes,ledger,pending = compose(prior,branch,control,args.branch_sha256,args.controls_sha256)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("arithmetic checked input changed during composition")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_source_closed_box":prior["actual_source_closed_box"],
        "source_file_sha256":prior["source_file_sha256"],
        "actual_checked919_predecessor_sha256":old.PRIOR_SHA,
        "actual_checked919_controls_sha256":old.PRIOR_CONTROL_SHA,
        "actual_complete_origin25_forest_diagnosis_sha256":args.branch_sha256,
        "actual_complete_origin25_forest_controls_sha256":args.controls_sha256,
        "new_entire_old_OPEN_leaf_excluded":2641,
        "nodes":nodes,"alternative_supports":prior["alternative_supports"],
        "full134rod_supports":prior["full134rod_supports"],
        "arithmetic_ledger":ledger,"pending_closed_leaf_boxes":pending,
        "remaining_OPEN_leaf_count":918,"total_whole_original_v4_OPEN_leaves_excluded":66,
        "all2999_old_domains_splits_supports_and581_prior_strict_rows_preserved":True,
        "complete_checked_origin25_forest_is_a_separate_bound_proof_NOT_an_old_full134_label":True,
        "all_earlier_math_qualified_REUSE_NOT_a_new_full_old_tree_replay":True,
        "this_is_only_checked_arithmetic_history_composition_NOT_geometry_cache":True,
        "new_independent_global_arithmetic_retention_controls_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"actual_checked_arithmetic_two_origin_composition_completed_NOT_admission":True,
                      "new_entire_old_OPEN_leaf":2641,"remaining_OPEN":918,
                      "all581old_strict_ledger_rows_retained":True,"formal_geometric_payments":0}),flush=True)


if __name__ == "__main__":
    main()
