"""Fresh ACTUAL current re-evaluation of two-owner pilot parameter certificates."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_origin_append_context_v3 as source
import probe_current_failed_origin_joint_refit_pilot_v1 as pilot
import n26_origin_branch_correlated_energy as energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-actual-current-missing-origin-owner-parameter-admission-v1"
PROOF = Path("work/n26-current-missing-origin-refit-admission-proof-v1.md")


def arguments(parser):
    source.arguments(parser)
    parser.add_argument("--pilot",type=Path,required=True)
    parser.add_argument("--pilot-sha256",required=True)


def inputs(args):
    values = source.inputs(args)
    original,model,seed,controls,row,pending,supports,kernels,references,arcs,inventory = values
    if binding.sha(args.pilot) != args.pilot_sha256:
        raise ValueError("actual completed missing-owner parameter pilot changed")
    old = binding.read(args.pilot)
    source.unpaid(old)
    if (
        old["schema"] != pilot.SCHEMA or old["source_OPEN_index"] != 25
        or old["actual_source_closed_box"] != row or old["source_file_sha256"] != seed["source_file_sha256"]
        or old["actual_current_seed_sha256"] != args.seed_sha256
        and seed.get("actual_current_predecessor_sha256") != old["actual_current_seed_sha256"]
        or old["executed_producer_sha256"] != binding.sha(pilot.__file__)
    ):
        raise ValueError("parameter pilot is not an actual immediate source/model ancestor")
    source.inventory_gate(old["input_sha256"])
    for text,digest in old["input_sha256"].items():
        if text in inventory and inventory[text] != digest:
            raise ValueError("current/parameter-pilot model digest conflict")
        inventory[text] = digest
    inventory.update({linux(args.pilot):args.pilot_sha256,linux(__file__):binding.sha(__file__),
                      linux(PROOF):binding.sha(PROOF),linux(energy.__file__):binding.sha(energy.__file__),
                      linux(energy.origin.__file__):binding.sha(energy.origin.__file__)})
    return values,old,inventory


def ownership(record,seed,pending):
    current = {leaf["index"]:leaf for leaf in pending}
    seen,strict = set(),set()
    for target in record["actual_current_two_owner_whole_trials"]:
        leaf = target["actual_current_whole_OPEN_leaf"]
        index = leaf["index"]
        if index in seen or current.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"}:
            raise ValueError("current origin target duplicated,clipped,paid or from an old snapshot")
        seen.add(index)
        branches = target["actual_whole_origin_branch_proofs"]
        if len(branches) != 2 or {proof["origin_center_label"] for proof in branches} != {16,25}:
            raise ValueError("current origin target omitted an entire original owner")
        for proof in branches:
            result,certificate = proof["arithmetic_result"],proof["certificate"]
            if (
                certificate["schema"] != energy.SCHEMA or certificate["origin_center_label"] != proof["origin_center_label"]
                or F(certificate["origin_multiplier"]) != F(proof["origin_multiplier"])
                or result["arithmetic_strict_entire_origin_branch"] is not True
                or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
            ):
                raise ValueError("current origin target contains an unbound/nonstrict owner")
        if target["BOTH_entire_actual_origin_branches_strict"] is not True:
            raise ValueError("current origin target paid only a partial owner proof")
        strict.add(index)
    if record["new_whole_actual_current_leaf_indices"] != sorted(strict):
        raise ValueError("current origin whole-payment subset differs")
    return strict


def scope(record,args,seed):
    source.unpaid(record)
    if (
        record["schema"] != SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_current_seed_file"] != linux(args.seed) or record["actual_current_seed_sha256"] != args.seed_sha256
        or record["actual_current_controls_file"] != linux(args.seed_controls)
        or record["actual_current_controls_sha256"] != args.seed_controls_sha256
        or record["parameter_pilot_sha256"] != args.pilot_sha256
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_current_OPEN_count"] != args.expected_open
        or record["old_current_nodes_tables_and_all_old_rows_UNMODIFIED"] is not True
        or record["executed_producer_sha256"] != binding.sha(__file__)
    ):
        raise ValueError("current origin parameter admission changed actual source,parent,scope or executor")


def main():
    parser = argparse.ArgumentParser()
    arguments(parser)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve current-bound origin parameter admission")
    values,old,inventory = inputs(args)
    original,model,seed,controls,row,pending,supports,kernels,references,arcs,_ = values
    current = {leaf["index"]:leaf for leaf in pending}
    results = []
    for target in old["actual_missing_owner_refit_whole_trials"]:
        leaf = target["actual_current_whole_OPEN_leaf"]
        if current.get(leaf["index"]) != leaf or seed["nodes"][leaf["index"]] != {"kind":"OPEN"}:
            raise ValueError("actual latest current lost or clipped a parameter-pilot whole target")
        keeper = target["retained_owner_parameter_proof_FRESHLY_recomputed"]
        support = keeper["base_full_support_index"]
        if type(support) is not int or not 0 <= support < len(kernels):
            raise ValueError("retained current origin owner names an unbound actual physical base")
        old_kernel = energy.origin.kernel_gate(
            kernels[support],original["data"][3],keeper["origin_center_label"],keeper["origin_multiplier"])
        old_result = energy.bound(old_kernel,original["matrix"],leaf["lower"],leaf["upper"],
                                  keeper["certificate"],original["radius"],arcs)
        new_base = energy.scalar.full.kernel_gate(model,target["fresh_physical_base_kernel_certificate"])
        new_kernel = energy.origin.kernel_gate(
            new_base,original["data"][3],target["actual_newly_refitted_owner"],target["fresh_origin_multiplier"])
        new_certificate = target["fresh_whole_origin_certificate"]
        new_result = energy.bound(new_kernel,original["matrix"],leaf["lower"],leaf["upper"],
                                  new_certificate,original["radius"],arcs)
        branches = [
            {"origin_center_label":keeper["origin_center_label"],"base_full_support_index":support,
             "origin_multiplier":keeper["origin_multiplier"],"certificate":keeper["certificate"],"arithmetic_result":old_result},
            {"origin_center_label":target["actual_newly_refitted_owner"],
             "fresh_physical_base_kernel_certificate":target["fresh_physical_base_kernel_certificate"],
             "fresh_base_reference_turns":target["fresh_joint_reference_turns"],
             "origin_multiplier":target["fresh_origin_multiplier"],"certificate":new_certificate,"arithmetic_result":new_result},
        ]
        results.append({"actual_current_whole_OPEN_leaf":leaf,"actual_whole_origin_branch_proofs":branches,
                        "BOTH_entire_actual_origin_branches_strict":all(
                            proof["arithmetic_result"]["arithmetic_strict_entire_origin_branch"] is True for proof in branches)})
        print(json.dumps({"actual_latest_origin_target":leaf["index"],"current_OPEN":args.expected_open,
                          "both_whole_current_owner_bounds_recomputed":True,
                          "old_pilot_not_relabelled_as_current":True}),flush=True)
    record = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "parameter_pilot_sha256":args.pilot_sha256,"actual_current_OPEN_count":args.expected_open,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "actual_current_two_owner_whole_trials":results,
        "new_whole_actual_current_leaf_indices":sorted(target["actual_current_whole_OPEN_leaf"]["index"] for target in results),
        "old_current_nodes_tables_and_all_old_rows_UNMODIFIED":True,
        "geometry_original26_premise_current_append_and_independent_controls_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    scope(record,args,seed)
    ownership(record,seed,pending)
    source.inventory_gate(inventory)
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(record,indent=2)+"\n")
    print(json.dumps({"actual_current_origin_parameter_admission_complete_NOT_append_or_geometry":True,
                      "whole_targets":len(results),"current_OPEN_UNMODIFIED":args.expected_open}),flush=True)


if __name__ == "__main__":
    main()
