"""Independent exact CURRENT physical bounds, all failures and checkpoint binding."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_reuse_source as source
import probe_current_physical_support_reuse as producer
import test_full134rod_correlated_support as arithmetic
import test_latest878_physical_donor_sweep as earlier_check
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-current-root25-physical-support-reuse-whole-leaf-controls-v1"


def scope(record, args, seed):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_current_seed_file"] != linux(args.seed)
        or record["actual_current_seed_sha256"] != args.seed_sha256
        or record["actual_current_controls_file"] != linux(args.seed_controls)
        or record["actual_current_controls_sha256"] != args.seed_controls_sha256
        or record["actual_current_OPEN_count"] != args.expected_open
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["old_current_global_nodes_supports_and_strict_rows_UNMODIFIED"] is not True
        or record["existing19_physical_supports_REUSED_NOT_appended_or_relabelled"] is not True
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("CURRENT physical reuse scope, parent, original source or executor changed")


def checkpoint_gate(record):
    actual = {item["actual_current_whole_OPEN_leaf"]["index"]:item for item in record["actual_current_whole_leaf_trials"]}
    seen, inventory = set(), {}
    for item in record["actual_immutable_attempt_checkpoints"]:
        index = item["whole_leaf_index"]
        if index in seen or index not in actual or binding.sha(item["path"]) != item["sha256"]:
            raise ValueError("CURRENT physical checkpoint repeated, omitted or changed")
        seen.add(index)
        point = binding.read(item["path"])
        if (
            point["schema"] != producer.CHECKPOINT_SCHEMA
            or point["actual_current_seed_sha256"] != record["actual_current_seed_sha256"]
            or point["actual_current_controls_sha256"] != record["actual_current_controls_sha256"]
            or point["actual_whole_leaf_trial"] != actual[index]
            or point["executed_producer_sha256"] != record["executed_producer_sha256"]
            or point["verified"] is not False or point["new_geometric_payments"] != 0
            or point["global_optimality_proved"] is not False
        ):
            raise ValueError("CURRENT physical checkpoint changed actual whole-domain strict/failed trial")
        inventory[item["path"]] = item["sha256"]
    if seen != set(actual):
        raise ValueError("CURRENT physical checkpoint list omits an attempted whole domain")
    return inventory


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed CURRENT physical batch and fresh independent output required")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("CURRENT physical primary prerequisite changed")
    original,model,seed,old_control,row,pending,supports,kernels,references,arcs,inventory = source.inputs(args)
    scope(record,args,seed)
    targets = source.ownership(record,seed,pending)
    checkpoint_inventory = checkpoint_gate(record)
    actual_domains,parents = source.domains.all_domains(original,row,seed["nodes"])
    checked,strict_whole,used = [],set(),set()
    for number,item in enumerate(record["actual_current_whole_leaf_trials"],1):
        leaf = item["actual_current_whole_OPEN_leaf"]
        index,proved = leaf["index"],False
        if actual_domains[index] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("CURRENT physical target clipped an independent entire source domain")
        for trial in item["actual_physical_support_trials"]:
            support = trial["full_support_index"]
            used.add(support)
            if trial["certificate"] is None:
                if trial["arithmetic_result"] is not None or trial["strict_entire_physical_leaf"] is not False:
                    raise ValueError("failed CURRENT physical LDL proposal forged as an exact result")
                checked.append({"whole_leaf_index":index,"full_support_index":support,
                                "no_exact_LDL_certificate":True,"strict_entire_physical_leaf":False})
                continue
            control = {"NEW_correlated_quadratic_certificate":trial["certificate"],
                       "NEW_correlated_exact_closed_leaf_result":trial["arithmetic_result"]}
            result = arithmetic.arithmetic_control(original,kernels[support],leaf,control,arcs)
            W = F(sum(kernels[support]["weights"]),kernels[support]["scale"])
            if F(result["NEW_full134rod_energy_upper_at_same_root"]) != original["radius"]**2*W:
                raise ValueError("CURRENT physical bound used a virtual origin budget")
            strict = result["arithmetic_strict_target_test_passed"]
            if strict != trial["strict_entire_physical_leaf"]:
                raise ValueError("independent CURRENT physical strict classification differs")
            if strict and (F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0):
                raise ValueError("independent CURRENT physical proof has no strict energy AND radius margin")
            proved |= strict
            checked.append({"whole_leaf_index":index,"full_support_index":support,
                            "strict_entire_physical_leaf":strict,"strict_radius_margin":result["strict_radius_margin"]})
        if item["strict_whole_physical_leaf"] != proved:
            raise ValueError("CURRENT physical whole-leaf strict subset differs independently")
        if proved:
            strict_whole.add(index)
        if number % 16 == 0 or number == len(record["actual_current_whole_leaf_trials"]) or not proved:
            print(json.dumps({"independent_CURRENT_whole_leaf_checks":number,
                              "of":len(record["actual_current_whole_leaf_trials"]),
                              "strict_whole_leaves":len(strict_whole),"last_whole_leaf":index}),flush=True)
    failed = sorted(item["actual_current_whole_OPEN_leaf"]["index"]
                    for item in record["actual_current_whole_leaf_trials"]
                    if item["actual_current_whole_OPEN_leaf"]["index"] not in strict_whole)
    if strict_whole != targets or record["actual_failed_whole_leaf_indices"] != failed:
        raise ValueError("independent CURRENT physical strict/failed whole-domain sets differ")
    if any(not earlier_check.root_positive(original,kernels[index]) for index in used):
        raise ValueError("CURRENT reused physical support falsely excludes the known exact covering root")
    rejected = []

    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid CURRENT physical reuse control accepted: "+label)

    reject("arithmetic-batch-promoted-to-global",lambda:scope({**record,"global_optimality_proved":True},args,seed))
    reject("current-pair-reset-to-old878",lambda:scope({
        **record,"actual_current_seed_sha256":source.earlier.SEED_SHA},args,seed))
    bad_args = argparse.Namespace(**vars(args))
    bad_args.expected_open += 1
    reject("current-parent-count-forged",lambda:source.paired(bad_args))
    if record["actual_current_whole_leaf_trials"]:
        bad = deepcopy(record)
        bad["actual_current_whole_leaf_trials"].append(deepcopy(bad["actual_current_whole_leaf_trials"][0]))
        reject("whole-current-target-duplicated",lambda:source.ownership(bad,seed,pending))
        bad = deepcopy(record)
        leaf = bad["actual_current_whole_leaf_trials"][0]["actual_current_whole_OPEN_leaf"]
        leaf["upper"][0] = str((F(leaf["lower"][0])+F(leaf["upper"][0]))/2)
        reject("proper-subbox-forged-as-entire-current-OPEN",lambda:source.ownership(bad,seed,pending))
        bad = deepcopy(record)
        bad["actual_current_whole_leaf_trials"][0]["actual_physical_support_trials"][0]["full_support_index"] = 19
        reject("reused-support-outside-unchanged19-table",lambda:source.ownership(bad,seed,pending))
        reject("immutable-current-attempt-omitted",lambda:checkpoint_gate({
            **record,"actual_immutable_attempt_checkpoints":record["actual_immutable_attempt_checkpoints"][:-1]}))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("CURRENT physical source changed during independent whole-domain arithmetic")
    for text,digest in checkpoint_inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("CURRENT immutable attempt changed during independent calculations")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("CURRENT physical diagnosis changed during independent calculations")
    inventory.update(record["input_sha256"])
    inventory.update(checkpoint_inventory)
    for module in (arithmetic,earlier_check):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_source_closed_box":row,
        "source_file_sha256":seed["source_file_sha256"],
        "all_actual_new_whole_physical_bounds_including_failures_independently_recomputed":checked,
        "new_strict_whole_leaf_indices":sorted(strict_whole),"actual_failed_whole_leaf_indices":failed,
        "prospective_remaining_OPEN_after_independent_join":args.expected_open-len(strict_whole),
        "all_old_current_nodes_supports_and_strict_rows_retained":True,
        "all19_actual_physical_inverse_identities_freshly_checked":True,
        "all_existing19_physical_supports_unchanged_NO_append":True,
        "known_exact_covering_root_not_excluded_by_any_used_physical_support":True,
        "no_origin_owner_or_virtual_mu_used_in_NEW_physical_proofs":True,
        "all_actual_immutable_attempt_checkpoints_rechecked":len(checkpoint_inventory),
        "actual_scope_owner_count_subset_support_and_checkpoint_rejection_controls":rejected,
        "old_mathematics_explicit_qualified_REUSE_NOT_fresh_all_history_replay":True,
        "current_global_tree_UNMODIFIED_separate_checked_history_join_STILL_required":True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "independent_CURRENT_physical_reuse_batch_completed_NOT_admission":True,
        "new_strict_whole_leaves":len(strict_whole),"retained_failed_whole_leaves":len(failed),
        "prospective_remaining_OPEN_PENDING_independent_join":args.expected_open-len(strict_whole),
        "actual_rejection_controls":len(rejected),
    }),flush=True)


if __name__ == "__main__":
    main()
