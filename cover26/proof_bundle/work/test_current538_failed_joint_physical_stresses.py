"""Independent fresh physical inverses/bounds and actual failed44 source identity."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_current538_failed_joint_physical_stresses as producer
import test_full134rod_correlated_support as arithmetic
import test_latest878_physical_donor_sweep as positive
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-current538-failed-whole-leaf-joint-fresh-physical-controls-v1"


def scope(record,args,seed):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_current_seed_file"] != linux(args.seed)
        or record["actual_current_seed_sha256"] != args.seed_sha256
        or record["actual_current_controls_file"] != linux(args.seed_controls)
        or record["actual_current_controls_sha256"] != args.seed_controls_sha256
        or record["actual_checked_prior_failed_diagnosis_sha256"] != producer.OLD_SHA
        or record["actual_checked_prior_failed_controls_sha256"] != producer.OLD_CONTROL_SHA
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["all962_old_strict_rows19supports_and_old_histories_UNMODIFIED"] is not True
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("fresh failed-joint physical scope/source/proof-time identity changed")


def main():
    parser = argparse.ArgumentParser()
    producer.source.arguments(parser)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed fresh failed-joint diagnosis and fresh controls required")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("fresh failed-joint original prerequisite changed")
    original,model,seed,old_control,row,pending,supports,kernels,ranked,arcs,inventory = producer.inputs(args)
    scope(record,args,seed)
    targets = producer.ownership(record,seed,pending)
    domains,parents = producer.source.domains.all_domains(original,row,seed["nodes"])
    checked,strict_whole,sample = [],set(),None
    for item in record["actual_failed_whole_leaf_fresh_trials"]:
        leaf = item["actual_current_failed_whole_OPEN_leaf"]
        index,proved = leaf["index"],False
        if domains[index] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("fresh failed-joint target clipped an independently reconstructed full domain")
        for trial in item["fresh_physical_trials"]:
            base = producer.source.earlier.suggestion.exact.full.kernel_gate(
                model,trial["fresh_physical_kernel_certificate"])
            if not positive.root_positive(original,base):
                raise ValueError("fresh failed-joint physical kernel falsely excludes the known exact root")
            if trial["certificate"] is None:
                if trial["arithmetic_result"] is not None or trial["strict_entire_physical_leaf"] is not False:
                    raise ValueError("rejected fresh failed-joint LDL proposal promoted to exact proof")
                checked.append({"whole_leaf_index":index,"no_exact_LDL_certificate":True,"strict_whole_leaf":False})
                continue
            if trial["certificate"]["reference_turns"] != trial["joint_reference_turns"]:
                raise ValueError("fresh failed-joint bound lost its actual exact joint reference")
            control = {"NEW_correlated_quadratic_certificate":trial["certificate"],
                       "NEW_correlated_exact_closed_leaf_result":trial["arithmetic_result"]}
            result = arithmetic.arithmetic_control(original,base,leaf,control,arcs)
            W = F(sum(base["weights"]),base["scale"])
            if F(result["NEW_full134rod_energy_upper_at_same_root"]) != original["radius"]**2*W:
                raise ValueError("fresh physical joint bound charged a virtual origin weight")
            strict = result["arithmetic_strict_target_test_passed"]
            if strict != trial["strict_entire_physical_leaf"]:
                raise ValueError("independent fresh failed-joint exact strict classification differs")
            proved |= strict
            if sample is None:
                sample = trial
            checked.append({"whole_leaf_index":index,
                            "numeric_initializer_owner_NOT_a_proof_condition":trial["origin_owner_for_numerical_initialization_ONLY"],
                            "strict_whole_leaf":strict,"strict_radius_margin":result["strict_radius_margin"]})
            print(json.dumps({"independent_new_physical_failed_whole_leaf":index,"strict":strict,
                              "actual_origin_owner_requirement":False}),flush=True)
        if proved != item["strict_whole_physical_leaf"]:
            raise ValueError("independent fresh failed-joint whole-target subset differs")
        if proved:
            strict_whole.add(index)
    if strict_whole != targets:
        raise ValueError("independent fresh failed-joint strict entire failed-domain set differs")
    rejected = []

    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid fresh failed-joint control accepted: "+label)

    reject("fresh-failed-joint-promoted-to-global",lambda:scope({**record,"global_optimality_proved":True},args,seed))
    reject("fresh-failed-joint-reset-to-prior750",lambda:scope({
        **record,"actual_current_seed_sha256":"cdcf4af2f24410908ce9bd59f82d521d4d62927e3fa97f631dc1d191ae59d0d2"},args,seed))
    if record["actual_failed_whole_leaf_fresh_trials"]:
        bad = deepcopy(record)
        bad["actual_failed_whole_leaf_fresh_trials"].append(deepcopy(bad["actual_failed_whole_leaf_fresh_trials"][0]))
        reject("fresh-failed-whole-domain-duplicated",lambda:producer.ownership(bad,seed,pending))
        bad = deepcopy(record)
        leaf = bad["actual_failed_whole_leaf_fresh_trials"][0]["actual_current_failed_whole_OPEN_leaf"]
        leaf["upper"][0] = str((F(leaf["lower"][0])+F(leaf["upper"][0]))/2)
        reject("fresh-subbox-forged-as-whole-old-failed-domain",lambda:producer.ownership(bad,seed,pending))
    if sample is not None:
        bad = deepcopy(sample["fresh_physical_kernel_certificate"])
        bad["weight_numerators"][0] = 0
        reject("fresh-physical-weight-zero",lambda:producer.source.earlier.suggestion.exact.full.kernel_gate(model,bad))
        bad = deepcopy(sample["fresh_physical_kernel_certificate"])
        bad["inverse_numerators"][0][0] = str(int(bad["inverse_numerators"][0][0])+1)
        reject("fresh60ground-inverse-corrupted",lambda:producer.source.earlier.suggestion.exact.full.kernel_gate(model,bad))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("fresh failed-joint source changed during independent arithmetic")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh failed-joint diagnosis changed during independent arithmetic")
    inventory.update(record["input_sha256"])
    for module in (arithmetic,positive):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_checked_prior_failed_diagnosis_sha256":producer.OLD_SHA,
        "actual_checked_prior_failed_controls_sha256":producer.OLD_CONTROL_SHA,
        "all_actual_fresh_physical_inverse_and_whole_bounds_including_failures_independently_checked":checked,
        "new_strict_whole_leaf_indices":sorted(strict_whole),
        "prospective_remaining_OPEN_after_independent_join":538-len(strict_whole),
        "all_original_failed44_sources_and_current538_domains_independently_retained":True,
        "all962_old_strict_rows19supports_and_old_histories_UNMODIFIED":True,
        "no_actual_origin_requirement_or_virtual_budget_in_new_PHYSICAL_proofs":True,
        "known_exact_covering_root_not_falsely_excluded_by_fresh_kernels":True,
        "actual_source_subset_inverse_weight_and_scope_rejection_controls":rejected,
        "old_mathematics_explicit_qualified_REUSE_NOT_fresh_all_history_replay":True,
        "current538_tree_UNMODIFIED_separate_checked_arithmetic_join_STILL_required":True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_fresh_failed_joint_physical_completed_NOT_admission":True,
                      "new_strict_old_FAILED_whole_leaves":len(strict_whole),
                      "prospective_remaining_OPEN_PENDING_independent_join":538-len(strict_whole),
                      "actual_rejection_controls":len(rejected)}),flush=True)


if __name__ == "__main__":
    main()
