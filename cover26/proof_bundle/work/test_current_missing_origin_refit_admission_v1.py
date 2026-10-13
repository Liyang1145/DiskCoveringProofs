"""Independent CURRENT two-owner inverse,budget and entire-domain admission."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import admit_current_missing_origin_refit_parameters_v1 as producer
import test_full_candidate_face_energy as physical
import test_full134rod_two_origin_kernel as augmented
import test_latest_root25_two_origin_whole_leaves as calculus
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-current-missing-origin-owner-admission-controls-v1"


def main():
    parser = argparse.ArgumentParser()
    producer.arguments(parser)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed current origin admission and fresh independent controls required")
    values,pilot,inventory = producer.inputs(args)
    original,model,seed,old_controls,row,pending,supports,bases,references,arcs,_ = values
    record = binding.read(args.diagnosis)
    producer.source.inventory_gate(record["input_sha256"])
    producer.scope(record,args,seed)
    strict = producer.ownership(record,seed,pending)
    actual,parents = producer.source.domains.all_domains(original,row,seed["nodes"])
    checks,identities = [],[]
    fresh_count = 0
    for target in record["actual_current_two_owner_whole_trials"]:
        leaf = target["actual_current_whole_OPEN_leaf"]
        index = leaf["index"]
        if actual[index] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("independent current origin admission clipped an actual entire domain")
        kernels,owners = [],set()
        for proof in target["actual_whole_origin_branch_proofs"]:
            owner,mu = proof["origin_center_label"],F(proof["origin_multiplier"])
            if "fresh_physical_base_kernel_certificate" in proof:
                if "base_full_support_index" in proof:
                    raise ValueError("new origin base forged as an existing physical support")
                base,physical_identity = physical.kernel_controls(model,proof["fresh_physical_base_kernel_certificate"])
                reference = proof["fresh_base_reference_turns"]
                producer.energy.scalar.full.hull.quadratic.reference_gate(
                    reference,leaf["lower"],leaf["upper"],original["matrix"])
                if proof["certificate"]["reference_turns"] != reference:
                    raise ValueError("fresh origin base reference differs from its actual whole certificate")
                fresh_count += 1
                base_role = "fresh"
            else:
                index_of_base = proof["base_full_support_index"]
                if type(index_of_base) is not int or not 0 <= index_of_base < len(supports):
                    raise ValueError("retained origin branch substituted an unbound physical base")
                base,physical_identity = physical.kernel_controls(model,supports[index_of_base]["kernel_certificate"])
                if base != bases[index_of_base]:
                    raise ValueError("retained current physical inverse differs independently")
                base_role = "retained"
            kernel = producer.energy.origin.kernel_gate(base,original["data"][3],owner,mu)
            identity = augmented.independent_identity(base,kernel)
            result = calculus.independent_arithmetic(original,kernel,leaf,{
                "certificate":proof["certificate"],"arithmetic_result":proof["arithmetic_result"]},arcs)
            if (
                result["arithmetic_strict_entire_origin_branch"] is not True
                or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
                or F(result["radius_squared_budget_W_PLUS_mu"]) != F(sum(base["weights"]),base["scale"])+mu
                or F(result["boundary_origin_constant"]) != kernel["boundary_origin_constant"]
            ):
                raise ValueError("independent current origin branch lost exact constant,budget or strictness")
            owners.add(owner)
            kernels.append(kernel)
            checks.append({"whole_leaf_index":index,"origin_center_label":owner,"base_role":base_role,
                           "strict_whole_origin_branch":True,"strict_radius_margin":result["strict_radius_margin"]})
            identities.append({"whole_leaf_index":index,"origin_center_label":owner,
                               "physical_identity":physical_identity,"augmented_identity":identity})
            print(json.dumps({"independent_current_whole_origin_leaf":index,"owner":owner,
                              "fresh_base":base_role == "fresh","strict":True}),flush=True)
        if owners != {16,25} or not any(calculus.root_positive(original,kernel) for kernel in kernels):
            raise ValueError("independent whole current origin union incomplete or falsely excludes the exact root")
    if fresh_count != len(strict):
        raise ValueError("current origin admission does not have one actual selected fresh base per whole target")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid current origin admission accepted: "+label)
    reject("arithmetic-promoted-to-global",lambda:producer.scope({**record,"global_optimality_proved":True},args,seed))
    reject("current-reset-to-pilot347",lambda:producer.scope({
        **record,"actual_current_seed_sha256":pilot["actual_current_seed_sha256"]},args,seed))
    targets = record["actual_current_two_owner_whole_trials"]
    reject("current-whole-target-duplicated",lambda:producer.ownership({
        **record,"actual_current_two_owner_whole_trials":[*targets,targets[0]]},seed,pending))
    changed = deepcopy(targets[0])
    changed["actual_whole_origin_branch_proofs"] = changed["actual_whole_origin_branch_proofs"][:1]
    reject("entire-owner-omitted",lambda:producer.ownership({
        **record,"actual_current_two_owner_whole_trials":[changed,*targets[1:]]},seed,pending))
    changed = deepcopy(targets[0])
    leaf = changed["actual_current_whole_OPEN_leaf"]
    axis = next(i for i,(a,b) in enumerate(zip(leaf["lower"],leaf["upper"])) if F(a) < F(b))
    leaf["upper"][axis] = str((F(leaf["lower"][axis])+F(leaf["upper"][axis]))/2)
    reject("proper-subbox-forged-entire-current-target",lambda:producer.ownership({
        **record,"actual_current_two_owner_whole_trials":[changed,*targets[1:]]},seed,pending))
    fresh_proof = next(proof for proof in targets[0]["actual_whole_origin_branch_proofs"]
                       if "fresh_physical_base_kernel_certificate" in proof)
    corrupted = deepcopy(fresh_proof["fresh_physical_base_kernel_certificate"])
    corrupted["inverse_numerators"][0][0] = str(int(corrupted["inverse_numerators"][0][0])+1)
    reject("fresh60ground-inverse-corrupted",lambda:physical.kernel_controls(model,corrupted))
    base,_ = physical.kernel_controls(model,fresh_proof["fresh_physical_base_kernel_certificate"])
    kernel = producer.energy.origin.kernel_gate(
        base,original["data"][3],fresh_proof["origin_center_label"],fresh_proof["origin_multiplier"])
    reject("virtual-mu-omitted-from-budget",lambda:augmented.independent_identity(
        base,{**kernel,"radius_squared_budget_weight":kernel["original_physical_rod_weight_sum"]}))
    reject("indispensable-origin-constant-omitted",lambda:augmented.independent_identity(
        base,{**kernel,"boundary_origin_constant":F(0)}))
    inventory.update(record["input_sha256"])
    for module in (physical,augmented,calculus):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    producer.source.inventory_gate(inventory)
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_seed_sha256":args.seed_sha256,"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_current_physical_support_count":args.expected_supports,
        "parameter_pilot_sha256":args.pilot_sha256,"actual_source_closed_box":row,
        "source_file_sha256":seed["source_file_sha256"],"new_whole_actual_current_leaf_indices":sorted(strict),
        "all_actual_current_owner_bounds_independently_recomputed":checks,
        "actual_physical_and_augmented_identity_controls":identities,
        "selected_NEW_physical_bases_independently_checked":fresh_count,
        "BOTH_whole_actual_origin_branches_checked_before_each_new_payment":True,
        "all_old_current_nodes_tables_and_rows_UNMODIFIED":True,
        "known_exact_root_not_falsely_excluded_by_each_complete_origin_union":True,
        "actual_source_owner_domain_inverse_constant_budget_and_scope_rejections":rejected,
        "current_append_independent_retention_and_latest_geometry_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_current_origin_admission_complete_NOT_append_or_geometry":True,
                      "whole_targets":len(strict),"selected_fresh_bases":fresh_count,
                      "actual_rejections":len(rejected)}),flush=True)


if __name__ == "__main__":
    main()
