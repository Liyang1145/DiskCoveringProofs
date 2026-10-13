"""Retain actual successful origin branches; freshly refit only missing owners.

All15angles and60free points may move numerically without symmetry. Fresh
positive physical weights,augmented inverse,constant,W+mu budget and exact
whole bounds decide success. No numerical minimum or current count is adopted.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_context_v2 as source
import probe_current_origin_multiplier_pilot_v1 as previous
import probe_latest918_joint_origin_stress_batch as numerical
import test_full_candidate_face_energy as physical_check
import test_full134rod_two_origin_kernel as origin_check
import test_latest_root25_two_origin_whole_leaves as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current-failed-owner-joint-origin-refit-pilot-v1"
PROOF = Path("work/n26-current-failed-owner-joint-origin-refit-proof-v1.md")


def recompute(original,base,leaf,owner,mu,certificate,result,arcs):
    kernel = numerical.energy.origin.kernel_gate(base,original["data"][3],owner,mu)
    identity = origin_check.independent_identity(base,kernel)
    if certificate is not None:
        actual = independent.independent_arithmetic(
            original,kernel,leaf,{"certificate":certificate,"arithmetic_result":result},arcs)
        if actual != result:
            raise ValueError("current missing-owner refit differs from separate exact arithmetic")
    elif result is not None:
        raise ValueError("current missing-owner refit forged an exact result after LDL failure")
    return kernel,identity


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--old-pilot",type=Path,required=True)
    parser.add_argument("--old-pilot-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=2)
    parser.add_argument("--parts",type=int,default=32)
    parser.add_argument("--iterations",type=int,default=900)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 3 or not 1 <= args.parts <= 64 or not 1 <= args.iterations <= 1500:
        raise ValueError("fresh bounded current missing-owner refit pilot required")
    if binding.sha(args.old_pilot) != args.old_pilot_sha256:
        raise ValueError("actual completed one-owner parameter pilot changed")
    old = binding.read(args.old_pilot)
    original,model,seed,controls,row,pending,supports,bases,turns,arcs,inventory = source.inputs(args)
    if (
        old["schema"] != previous.SCHEMA or old["source_OPEN_index"] != 25
        or old["actual_source_closed_box"] != row or old["source_file_sha256"] != seed["source_file_sha256"]
        or old["verified"] is not False or old["new_geometric_payments"] != 0
        or old["global_optimality_proved"] is not False
        or old["actual_current_seed_sha256"] != args.seed_sha256
        and seed.get("actual_current_predecessor_sha256") != old["actual_current_seed_sha256"]
    ):
        raise ValueError("missing-owner refit lost the actual source/model or immediate current lineage")
    for text,digest in old["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("old one-owner parameter evidence changed")
        if text in inventory and inventory[text] != digest:
            raise ValueError("current/old one-owner model digest conflict")
        inventory[text] = digest
    actual = {leaf["index"]:leaf for leaf in pending}
    selected = []
    for target in old["actual_positive_origin_whole_domain_pilot_trials"]:
        leaf = target["actual_current_failed_whole_OPEN_leaf"]
        if len(target["strict_origin_branch_proofs"]) != 1:
            continue
        if target["BOTH_whole_origin_branches_strict"] is not False:
            raise ValueError("missing-owner refit attempted a prior whole-success case")
        if actual.get(leaf["index"]) != leaf or seed["nodes"][leaf["index"]] != {"kind":"OPEN"}:
            raise ValueError("missing-owner refit clipped or re-paid an actual current whole domain")
        selected.append(target)
    if len(selected) < args.limit:
        raise ValueError("missing-owner refit lacks enough actually retained partial successes")
    for module in (previous,numerical,numerical.fresh,numerical.energy,physical_check,origin_check,independent):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.old_pilot):args.old_pilot_sha256,linux(__file__):binding.sha(__file__),
                      linux(PROOF):binding.sha(PROOF)})
    results = []
    print(json.dumps({"actual_partial_owner_successes":len(selected),"fresh_missing_owner_targets":args.limit,
                      "no_symmetry_no_point_minimum_proof_no_current_payment":True}),flush=True)
    for target in selected[:args.limit]:
        leaf = target["actual_current_failed_whole_OPEN_leaf"]
        keeper = target["strict_origin_branch_proofs"][0]
        kept_owner,kept_support = keeper["origin_center_label"],keeper["base_full_support_index"]
        kept_kernel,kept_identity = recompute(
            original,bases[kept_support],leaf,kept_owner,keeper["origin_multiplier"],
            keeper["certificate"],keeper["arithmetic_result"],arcs)
        if (
            keeper["arithmetic_result"]["arithmetic_strict_entire_origin_branch"] is not True
            or F(keeper["arithmetic_result"]["strict_energy_margin"]) <= 0
            or F(keeper["arithmetic_result"]["strict_radius_margin"]) <= 0
        ):
            raise ValueError("actually retained whole first-owner proof is no longer strict")
        owner = next(value for value in (16,25) if value != kept_owner)
        failed = [trial for trial in target["actual_new_origin_branch_trials"] if trial["origin_center_label"] == owner]
        usable = [trial for trial in failed if trial["arithmetic_result"] is not None]
        start = max(usable,key=lambda trial:F(trial["arithmetic_result"]["strict_radius_margin"])) if usable else failed[0]
        turns,points,primal = numerical.joint_suggestion(
            original,model,bases[start["base_full_support_index"]],leaf,owner,args.iterations)
        weights,mu,fit = numerical.stress_suggestion(model,turns,points,owner)
        base_certificate,base = numerical.fresh.exact_base(model,weights)
        independently_checked,physical_identity = physical_check.kernel_controls(model,base_certificate)
        if independently_checked != base:
            raise ValueError("new missing-owner physical inverse disagrees independently")
        multiplier = F(max(0,round(float(mu)*10**30)),10**30)
        kernel = numerical.energy.origin.kernel_gate(base,original["data"][3],owner,multiplier)
        certificate,result,suggestions = numerical.energy.suggest(
            kernel,original["matrix"],list(map(F,leaf["lower"])),list(map(F,leaf["upper"])),
            turns,original["radius"],arcs,args.parts)
        new_kernel,new_identity = recompute(
            original,base,leaf,owner,multiplier,certificate,result,arcs)
        strict = bool(result is not None and result["arithmetic_strict_entire_origin_branch"] is True)
        if strict and not any(independent.root_positive(original,item) for item in (kept_kernel,new_kernel)):
            raise ValueError("fresh missing-owner complete union falsely excludes the known exact root")
        item = {
            "actual_current_whole_OPEN_leaf":leaf,"actually_retained_whole_owner":kept_owner,
            "retained_owner_parameter_proof_FRESHLY_recomputed":keeper,
            "retained_owner_augmented_identity":kept_identity,
            "actual_newly_refitted_owner":owner,"fresh_physical_base_kernel_certificate":base_certificate,
            "fresh_physical_independent_identity":physical_identity,"fresh_origin_multiplier":str(multiplier),
            "fresh_joint_reference_turns":list(map(str,turns)),"numerical_rational60_free_points_NOT_proof":points,
            "fresh_whole_origin_certificate":certificate,"fresh_whole_origin_result":result,
            "fresh_augmented_origin_identity":new_identity,"fresh_entire_missing_owner_strict":strict,
            "BOTH_whole_original_origin_branches_strict":strict,
            "numerical_joint_suggestion_NOT_proof":primal,"numerical_stress_fit_NOT_proof":fit,
            "numerical_curvature_suggestions_NOT_proof":suggestions,
        }
        results.append(item)
        print(json.dumps({"actual_current_whole_leaf":leaf["index"],"retained_strict_owner":kept_owner,
                          "newly_refitted_owner":owner,"fresh_missing_owner_strict":strict,
                          "fresh_radius_margin_display":float(F(result["strict_radius_margin"])) if result else None,
                          "BOTH_whole_branches_strict":strict,"current_OPEN_count_UNMODIFIED":args.expected_open}),
              flush=True)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("missing-owner refit source/model/code changed during fresh exact calculations")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "old_partial_owner_pilot_PARAMETER_DATA_sha256":args.old_pilot_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_missing_owner_refit_whole_trials":results,
        "old_successful_owner_preserved_with_FRESH_whole_bound_recomputation":True,
        "all_NEW_physical_and_augmented_inverses_constants_W_PLUS_mu_and_bounds_checked":True,
        "no_current_nodes_support_tables_rows_or_counts_changed":True,
        "latest_source_geometry_original26_premise_and_separate_current_batch_join_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"current_missing_owner_joint_refit_pilot_complete_NO_count_change":True,
                      "whole_domains":len(results),
                      "both_owner_whole_successes":sum(item["BOTH_whole_original_origin_branches_strict"] for item in results)}),
          flush=True)


if __name__ == "__main__":
    main()
