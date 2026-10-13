"""Independent latest whole-leaf successor bounds and checked history retention."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_latest_root25_balanced_whole_leaf_energy as producer
import test_checked_root28_full134rod_intersections as domains
import test_full134rod_correlated_support as energy
import verify_conditional_force_stage as binding


def scope(record,seed,row,args):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != row
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_checked_predecessor_sha256"] != args.seed_sha256
        or record["actual_checked_predecessor_controls_sha256"] != args.seed_controls_sha256
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or record["unchanged_prior_arithmetic_explicitly_REUSED_NOT_fresh_all_old_leaf_replays"] is not True
        or any(record[field] is not False for field in (
            "global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("independent latest successor scope/history/executor changed")


def retention(record,seed,pending):
    by_index = {leaf["index"]:leaf for leaf in pending}
    nodes,ledger = deepcopy(seed["nodes"]),deepcopy(seed["arithmetic_ledger"])
    seen = set()
    for target in record["new_exact_strict_whole_old_OPEN_leaves"]:
        leaf,index = target["actual_prior_OPEN_leaf"],target["actual_prior_OPEN_leaf"]["index"]
        support = target["full_support_index"]
        if (
            index in seen or by_index.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"}
            or type(support) is not int or not 0 <= support < len(seed["full134rod_supports"])
            or target["entire_actual_prior_OPEN_leaf_strict"] is not True
        ):
            raise ValueError("latest whole-leaf target is not a unique entire prior OPEN")
        seen.add(index)
        nodes[index] = {"kind":producer.first.mixed.KIND,"full_support_index":support,
                        "certificate":target["certificate"]}
        ledger.append({**leaf,"kind":producer.first.mixed.KIND,"full_support_index":support,
                       "certificate":target["certificate"],"arithmetic_result":target["arithmetic_result"]})
    ledger.sort(key=lambda row:row["index"])
    remaining = [leaf for leaf in pending if leaf["index"] not in seen]
    if (
        record["nodes"] != nodes or record["arithmetic_ledger"] != ledger
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["full134rod_supports"] != seed["full134rod_supports"]
        or record["pending_closed_leaf_boxes"] != remaining
        or record["remaining_OPEN_leaf_count"] != len(remaining)
        or record["prior_OPEN_leaf_count"] != len(pending)
        or record["new_exact_strict_whole_old_OPEN_leaf_count"] != len(seen)
        or record["total_strict_whole_original_v4_OPEN_leaves"] != 984-len(remaining)
        or len(remaining)+len(seen) != len(pending)
    ):
        raise ValueError("latest successor changed prior arithmetic or lost unproved whole leaves")
    return remaining


def main():
    parser = argparse.ArgumentParser()
    for name in ("seed","seed-controls","diagnosis","report"):
        parser.add_argument("--"+name,type=Path,required=True)
    for name in ("seed-sha256","seed-controls-sha256","diagnosis-sha256"):
        parser.add_argument("--"+name,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("latest independent controls need fresh output and exact completed diagnosis")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("latest successor dependency changed before independent controls")
    original,model,kernels,seed,prior_controls,row,pending,arcs,inventory = producer.source(args)
    scope(record,seed,row,args)
    remaining = retention(record,seed,pending)
    retained = producer.first.mixed.retention_gate(seed,record)
    if list(retained) != record["immutable_checked_predecessor_node_support_and_strict_ledger_retention"]:
        raise ValueError("latest exact retained node/support/strict-ledger counts differ")
    before,parents = domains.all_domains(original,row,seed["nodes"])
    after,after_parents = domains.all_domains(original,row,record["nodes"])
    if before != after or parents != after_parents:
        raise ValueError("latest successor changed an old split/domain/shared boundary")
    targets = record["new_exact_strict_whole_old_OPEN_leaves"]
    checked,margins = [],[]
    for number,target in enumerate(targets,1):
        leaf,support = target["actual_prior_OPEN_leaf"],target["full_support_index"]
        if before[leaf["index"]] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("independent latest whole-leaf bounds differ")
        trial = {"NEW_correlated_quadratic_certificate":target["certificate"],
                 "NEW_correlated_exact_closed_leaf_result":target["arithmetic_result"]}
        result = energy.arithmetic_control(original,kernels[support],leaf,trial,arcs)
        if (
            result["arithmetic_strict_target_test_passed"] is not True
            or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
        ):
            raise ValueError("latest independent strict entire-leaf bound failed")
        margins.append(F(result["strict_radius_margin"]))
        checked.append({"actual_prior_OPEN_leaf_index":leaf["index"],"full_support_index":support,
                        "strict_radius_margin":result["strict_radius_margin"]})
        if number%8 == 0 or number == len(targets):
            print(json.dumps({"independent_NEW_whole_leaf_bounds":number,"of":len(targets),
                              "strict":True,"formal_geometric_payments":0}),flush=True)
    by_index = {leaf["index"]:leaf for leaf in pending}
    attempts,positive = set(),set()
    for item in record["all_actual_attempts"]:
        leaf = item["actual_prior_OPEN_leaf"]
        index = leaf["index"]
        if index in attempts or by_index.get(index) != leaf:
            raise ValueError("latest attempted leaf owner repeated or changed")
        attempts.add(index)
        result = item["arithmetic_result"]
        strict = result is not None and result["arithmetic_strict_target_test_passed"] is True
        if strict != item["entire_actual_prior_OPEN_leaf_strict"]:
            raise ValueError("latest exact strict attempt classification changed")
        if strict:
            positive.add(index)
    if positive != {target["actual_prior_OPEN_leaf"]["index"] for target in targets}:
        raise ValueError("latest strict target list lost an actual positive whole-leaf attempt")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid latest whole-leaf control accepted: "+label)
    changed = {**record,"global_optimality_proved":True}
    reject("latest-arithmetic-promoted-to-global",lambda:scope(changed,seed,row,args))
    changed = deepcopy(record)
    changed["pending_closed_leaf_boxes"].pop()
    reject("latest-unpaid-leaf-omitted",lambda:retention(changed,seed,pending))
    changed = deepcopy(record)
    paid_index = next(i for i,node in enumerate(seed["nodes"]) if node["kind"] != "OPEN")
    changed["nodes"][paid_index] = {"kind":"OPEN"}
    reject("checked-prior-nonOPEN-reset",lambda:retention(changed,seed,pending))
    changed = deepcopy(record)
    changed["arithmetic_ledger"].pop(0)
    reject("checked-prior-ledger-row-lost",lambda:retention(changed,seed,pending))
    changed = deepcopy(record)
    changed["full134rod_supports"].pop()
    reject("checked-prior-support-truncated",lambda:retention(changed,seed,pending))
    if targets:
        changed = deepcopy(record)
        changed["new_exact_strict_whole_old_OPEN_leaves"].append(deepcopy(targets[0]))
        reject("latest-entire-leaf-paid-twice",lambda:retention(changed,seed,pending))
        changed = deepcopy(record)
        leaf = changed["new_exact_strict_whole_old_OPEN_leaves"][0]["actual_prior_OPEN_leaf"]
        leaf["upper"][0] = str((F(leaf["lower"][0])+F(leaf["upper"][0]))/2)
        reject("latest-proper-subbox-forged-as-whole",lambda:retention(changed,seed,pending))
        changed = deepcopy(record)
        changed["new_exact_strict_whole_old_OPEN_leaves"][0]["full_support_index"] = -1
        reject("latest-invalid-support-owner",lambda:retention(changed,seed,pending))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("latest successor evidence changed during independent arithmetic")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("latest diagnosis changed during independent arithmetic")
    inventory.update({
        linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__),
        linux(domains.__file__):binding.sha(domains.__file__),
        linux(energy.__file__):binding.sha(energy.__file__),
    })
    report = {
        "schema":producer.CONTROL_SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "diagnosis_sha256":args.diagnosis_sha256,
        "actual_checked_predecessor_sha256":args.seed_sha256,
        "actual_checked_predecessor_controls_sha256":args.seed_controls_sha256,
        "all_original_closed_domains_shared_boundaries_AND_prior_payments_independently_retained":True,
        "prior_node_support_and_strict_ledger_retention_counts":list(retained),
        "all_NEW_actual_whole_leaf_bounds_independently_recomputed":checked,
        "new_strict_whole_old_OPEN_leaf_count":len(checked),
        "remaining_OPEN_leaf_count":len(remaining),
        "total_strict_whole_original_v4_OPEN_leaves":984-len(remaining),
        "minimum_NEW_strict_radius_margin":str(min(margins)) if margins else None,
        "independent_feasible_sine_square_and_positive_square_completion_controls":3*len(checked),
        "old_arithmetic_qualified_REUSE_NOT_fresh_old_leaf_replay":True,
        "actual_retention_scope_subset_and_target_rejection_controls":rejected,
        "arithmetic_only_NOT_latest_source_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "independent_latest_whole_leaf_successor_controls_completed_NOT_admission":True,
        "new_whole_leaves":len(checked),"remaining_OPEN":len(remaining),
        "total_strict_whole_original_v4_OPEN_leaves":984-len(remaining),
        "actual_rejection_controls":len(rejected),"global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
