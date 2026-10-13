"""Independent fresh134 inverse/origin bounds and immutable6+2 branch history."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_joint_fresh_origin25_stress_successor as producer
import test_latest_origin_branch_closed_forest as independent_domains
import test_latest_root25_two_origin_whole_leaves as independent_energy
import test_full134rod_two_origin_kernel as independent_kernel
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-joint-reference-origin25-fresh-stress-successor-controls-v1"


def retention(record,seed,pending):
    nodes,ledger = deepcopy(seed["origin25_closed_forest_nodes"]),deepcopy(seed["new_strict_origin25_subleaf_ledger"])
    by_index = {leaf["index"]:leaf for leaf in pending}
    supports = record["fresh_positive_origin25_supports"]
    seen = set()
    for target in record["new_strict_origin25_subleaf_targets"]:
        index = target["index"]
        support = target["fresh_support_index"]
        if (
            index in seen or index not in by_index or nodes[index] != {"kind":"OPEN"}
            or target["lower"] != by_index[index]["lower"] or target["upper"] != by_index[index]["upper"]
            or type(support) is not int or not 0 <= support < len(supports)
            or target["kind"] != producer.KIND
            or target["arithmetic_result"]["arithmetic_strict_entire_origin_branch"] is not True
        ):
            raise ValueError("fresh origin support target is not an entire unique actual retained OPEN")
        seen.add(index)
        nodes[index] = {"kind":producer.KIND,"fresh_support_index":support,"certificate":target["certificate"]}
        ledger.append(target)
    ledger.sort(key=lambda item:item["index"])
    if nodes != record["origin25_closed_forest_nodes"] or ledger != record["strict_origin25_subleaf_ledger"]:
        raise ValueError("fresh origin successor changed a prior split/proof/strict ledger")
    remaining = [leaf for leaf in pending if leaf["index"] not in seen]
    if (
        record["retained_origin25_OPEN_subleaves"] != remaining
        or record["entire_origin25_branch_strictly_excluded"] != (not remaining)
        or record["both_checked_origin_branches_arithmetically_exclude_whole_leaf2641"] != (not remaining)
    ):
        raise ValueError("fresh origin successor lost OPEN/complete second-branch classification")
    return remaining


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh exact completed positive-origin diagnostic required")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("fresh origin primary dependency changed")
    original,model,bases,seed,pending,primal,arcs,inventory = producer.inputs()
    if (
        record["schema"] != producer.SCHEMA
        or record["actual_prior_whole_leaf"] != seed["actual_latest919_OPEN_leaf"]
        or record["whole_origin16_branch_prior_checked_proof"] != seed["whole_origin16_branch_prior_checked_proof"]
        or record["actual_checked_partial_origin25_seed_sha256"] != producer.source.SEED_SHA
        or record["actual_checked_partial_origin25_controls_sha256"] != producer.source.CONTROL_SHA
        or record["actual_latest919_global_predecessor_sha256"] != producer.source.source.PRIOR_SHA
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or any(record[field] is not False for field in (
            "global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("fresh origin successor changed whole owner/otherbranch/prior proof/unpaid scope")
    remaining = retention(record,seed,pending)
    view = [
        {"kind":"ORIGIN-ENERGY","certificate":node["certificate"]} if node["kind"] == producer.KIND else deepcopy(node)
        for node in record["origin25_closed_forest_nodes"]
    ]
    before,before_leaves = independent_domains.independent_partition(
        original["matrix"],seed["actual_latest919_OPEN_leaf"],seed["origin25_closed_forest_nodes"])
    after,after_leaves = independent_domains.independent_partition(
        original["matrix"],seed["actual_latest919_OPEN_leaf"],view)
    if before != after:
        raise ValueError("fresh origin successor changed any complete old15 closed domain")
    kernels,identities = [],[]
    for support in record["fresh_positive_origin25_supports"]:
        base = producer.energy.scalar.full.kernel_gate(model,support["base_kernel_certificate"])
        kernel = producer.energy.origin.kernel_gate(base,original["data"][3],25,support["origin_multiplier"])
        identities.append(independent_kernel.independent_identity(base,kernel))
        kernels.append(kernel)
    checked = []
    for target in record["new_strict_origin25_subleaf_targets"]:
        index,support = target["index"],target["fresh_support_index"]
        leaf = {"index":index,"kind":"OPEN","lower":target["lower"],"upper":target["upper"]}
        if after[index] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("fresh strict origin target omitted part of actual whole retained box")
        trial = {"certificate":target["certificate"],"arithmetic_result":target["arithmetic_result"]}
        result = independent_energy.independent_arithmetic(original,kernels[support],leaf,trial,arcs)
        if (
            result["arithmetic_strict_entire_origin_branch"] is not True
            or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
        ):
            raise ValueError("fresh independent exact whole-origin subleaf bound is not strict")
        checked.append({"actual_old_OPEN_subleaf_index":index,"fresh_support_index":support,
                        "strict_radius_margin":result["strict_radius_margin"]})
        print(json.dumps({"independent_fresh_origin25_whole_subleaf":index,"strict":True,
                          "complete_branch_cover_checked":not remaining}),flush=True)
    actual = {item["actual_latest_origin25_OPEN_subleaf"]["index"]:item for item in record["actual_fresh_stress_trials"]}
    if len(actual) != len(record["actual_fresh_stress_trials"]) or set(actual) != {leaf["index"] for leaf in pending}:
        raise ValueError("fresh actual attempted support list omitted/duplicated retained source")
    attempted_checks = []
    for index,item in actual.items():
        base = producer.energy.scalar.full.kernel_gate(model,item["fresh_positive134rod_kernel_certificate"])
        kernel = producer.energy.origin.kernel_gate(base,original["data"][3],25,item["fresh_origin_multiplier"])
        independent_kernel.independent_identity(base,kernel)
        if item["whole_subleaf_origin_certificate"] is not None:
            trial = {"certificate":item["whole_subleaf_origin_certificate"],
                     "arithmetic_result":item["whole_subleaf_origin_arithmetic_result"]}
            result = independent_energy.independent_arithmetic(
                original,kernel,item["actual_latest_origin25_OPEN_subleaf"],trial,arcs)
            if result["arithmetic_strict_entire_origin_branch"] != item["fresh_actual_whole_subleaf_strict"]:
                raise ValueError("independent actual fresh stress attempt strict classification differs")
            attempted_checks.append({"actual_retained_OPEN_subleaf_index":index,
                                     "strict_whole_subleaf":result["arithmetic_strict_entire_origin_branch"]})
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid fresh origin successor control accepted: "+label)
    bad = deepcopy(record)
    bad["strict_origin25_subleaf_ledger"].pop(0)
    reject("prior6-strict-ledger-row-lost",lambda:retention(bad,seed,pending))
    bad = deepcopy(record)
    old_index = next(i for i,node in enumerate(seed["origin25_closed_forest_nodes"]) if node["kind"] == "ORIGIN-ENERGY")
    bad["origin25_closed_forest_nodes"][old_index] = {"kind":"OPEN"}
    reject("prior6-strict-node-reset",lambda:retention(bad,seed,pending))
    if record["new_strict_origin25_subleaf_targets"]:
        bad = deepcopy(record)
        bad["new_strict_origin25_subleaf_targets"].append(deepcopy(bad["new_strict_origin25_subleaf_targets"][0]))
        reject("fresh-origin-target-repeated",lambda:retention(bad,seed,pending))
        bad = deepcopy(record)
        target = bad["new_strict_origin25_subleaf_targets"][0]
        target["upper"][0] = str((F(target["lower"][0])+F(target["upper"][0]))/2)
        reject("fresh-proper-subbox-forged-whole-OPEN",lambda:retention(bad,seed,pending))
        bad = deepcopy(record)
        bad["new_strict_origin25_subleaf_targets"][0]["fresh_support_index"] = -1
        reject("fresh-origin-support-owner-invalid",lambda:retention(bad,seed,pending))
    if record["fresh_positive_origin25_supports"]:
        support = record["fresh_positive_origin25_supports"][0]
        bad = deepcopy(support["base_kernel_certificate"])
        bad["inverse_numerators"][0][0] = str(int(bad["inverse_numerators"][0][0])+1)
        reject("fresh60ground-inverse-corrupted",lambda:producer.energy.scalar.full.kernel_gate(model,bad))
        bad = deepcopy(support["base_kernel_certificate"])
        bad["weight_numerators"][0] = 0
        reject("fresh-original-rod-weight-nonpositive",lambda:producer.energy.scalar.full.kernel_gate(model,bad))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("fresh origin evidence changed during independent arithmetic")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh origin diagnostic changed during independent arithmetic")
    inventory.update(record["input_sha256"])
    inventory.update({
        linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__),
        linux(independent_domains.__file__):binding.sha(independent_domains.__file__),
        linux(independent_energy.__file__):binding.sha(independent_energy.__file__),
        linux(independent_kernel.__file__):binding.sha(independent_kernel.__file__),
    })
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_prior_whole_leaf":seed["actual_latest919_OPEN_leaf"],
        "actual_checked_partial_origin25_seed_sha256":producer.source.SEED_SHA,
        "actual_checked_partial_origin25_controls_sha256":producer.source.CONTROL_SHA,
        "actual_latest919_global_predecessor_sha256":producer.source.source.PRIOR_SHA,
        "fresh134ground_and_augmented_origin_inverse_square_completions":identities,
        "all_NEW_strict_entire_origin25_subleaf_bounds_independently_recomputed":checked,
        "all_actual_fresh_origin_stress_attempts_including_failures_independently_recomputed":attempted_checks,
        "independent_sine_secant_tangent_point_controls":3*len(checked),
        "all_old15_domains_and6prior_strict_rows_preserved_independently":True,
        "retained_origin25_OPEN_subleaves":remaining,
        "entire_origin25_branch_strictly_excluded":not remaining,
        "both_checked_origin_branches_arithmetically_exclude_whole_leaf2641":not remaining,
        "latest919_global_tree_and581old_strict_rows_UNMODIFIED":True,
        "old_checked_arithmetic_qualified_REUSE_NOT_full_prior_replay":True,
        "actual_retention_subset_support_inverse_and_weight_rejection_controls":rejected,
        "arithmetic_only_NOT_latest_source_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "independent_fresh_origin25_stress_successor_controls_completed_NOT_admission":True,
        "new_whole_partial_OPEN_subleaves":len(checked),"remaining_origin25_OPEN":len(remaining),
        "whole_old_leaf2641_arithmetic_excluded":not remaining,"actual_rejection_controls":len(rejected),
    }),flush=True)


if __name__ == "__main__":
    main()
