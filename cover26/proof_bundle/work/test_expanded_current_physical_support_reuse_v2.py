"""Independent expanded-table inverses, whole bounds, failures and checkpoints."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_context_v2 as source
import probe_expanded_current_physical_support_reuse_v2 as producer
import test_full_candidate_face_energy as inverse_check
import test_full134rod_correlated_support as arithmetic
import test_latest878_physical_donor_sweep as positive
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-current-root25-expanded-physical-reuse-whole-controls-v2"


def scope(record,args,seed):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_current_seed_file"] != linux(args.seed)
        or record["actual_current_seed_sha256"] != args.seed_sha256
        or record["actual_current_controls_file"] != linux(args.seed_controls)
        or record["actual_current_controls_sha256"] != args.seed_controls_sha256
        or record["actual_current_OPEN_count"] != args.expected_open
        or record["actual_current_support_count"] != args.expected_supports
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["old_current_nodes_supports_and_strict_rows_UNMODIFIED"] is not True
        or record["expanded_actual_physical_support_table_reused_unchanged_NO_append"] is not True
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("expanded physical batch changed actual parent,table,source,executor or scope")
    method = record["method_parameters"]
    if (
        type(method["parts"]) is not int or not 1 <= method["parts"] <= 64
        or type(method["support_tries"]) is not int or not 1 <= method["support_tries"] <= args.expected_supports
        or method["reference_strategy"] != "exact_projection_of_expanded_current_support_reference"
        or method["new_physical_support_prefix_starts_at"] != 19
        or method["failed_first_attempt_prioritizes_best_new_physical_support"] is not True
        or not record["actual_current_whole_leaf_trials"]
    ):
        raise ValueError("expanded physical batch lost bounded actual new-support attempt strategy")
    for target in record["actual_current_whole_leaf_trials"]:
        trials = target["actual_physical_support_trials"]
        indices = [trial["full_support_index"] for trial in trials]
        if (
            not 1 <= len(trials) <= method["support_tries"] or len(set(indices)) != len(indices)
            or any(trial["certificate"] is not None and trial["certificate"]["parts"] != method["parts"]
                   for trial in trials)
            or len(trials) > 1 and indices[0] < 19 and indices[1] < 19
        ):
            raise ValueError("expanded physical batch repeated old failed supports or changed Taylor strips")


def checkpoint_gate(record):
    actual = {target["actual_current_whole_OPEN_leaf"]["index"]:target
              for target in record["actual_current_whole_leaf_trials"]}
    if len(actual) != len(record["actual_current_whole_leaf_trials"]):
        raise ValueError("expanded checkpoint owner duplicated")
    seen,inventory = set(),{}
    for item in record["actual_immutable_attempt_checkpoints"]:
        index = item["whole_leaf_index"]
        if index in seen or index not in actual or binding.sha(item["path"]) != item["sha256"]:
            raise ValueError("expanded physical checkpoint repeated,omitted or changed")
        seen.add(index)
        checkpoint = binding.read(item["path"])
        if (
            checkpoint["schema"] != producer.CHECKPOINT_SCHEMA
            or checkpoint["actual_current_seed_sha256"] != record["actual_current_seed_sha256"]
            or checkpoint["actual_current_controls_sha256"] != record["actual_current_controls_sha256"]
            or checkpoint["actual_whole_leaf_trial"] != actual[index]
            or checkpoint["executed_producer_sha256"] != record["executed_producer_sha256"]
            or checkpoint["verified"] is not False or checkpoint["new_geometric_payments"] != 0
            or checkpoint["global_optimality_proved"] is not False
        ):
            raise ValueError("expanded physical checkpoint does not bind an actual whole-domain trial")
        inventory[item["path"]] = item["sha256"]
    if seen != set(actual):
        raise ValueError("expanded physical checkpoint list omits an entire attempted domain")
    return inventory


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed expanded physical batch and fresh independent output required")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("expanded physical primary prerequisite changed")
    original,model,seed,old_controls,row,pending,supports,kernels,references,arcs,inventory = source.inputs(args)
    scope(record,args,seed)
    targets = source.ownership(record,seed,pending)
    checkpoints = checkpoint_gate(record)
    # Fresh independent incidence construction and inverse*ground product
    # for every actual current support,including all eight newly appended ones.
    for index,support in enumerate(supports):
        independently_checked,identity = inverse_check.kernel_controls(model,support["kernel_certificate"])
        if independently_checked != kernels[index] or not positive.root_positive(original,independently_checked):
            raise ValueError("expanded support inverse/source mismatch or known exact root excluded")
        if (index+1) % 8 == 0 or index+1 == len(supports):
            print(json.dumps({"independent_expanded_physical_inverses":index+1,
                              "of":len(supports),"known_exact_root_retained":True}),flush=True)
    actual_domains,parents = source.domains.all_domains(original,row,seed["nodes"])
    checked,strict_whole = [],set()
    for number,target in enumerate(record["actual_current_whole_leaf_trials"],1):
        leaf = target["actual_current_whole_OPEN_leaf"]
        index,proved = leaf["index"],False
        if actual_domains[index] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("expanded physical target clipped an independent entire current domain")
        for trial in target["actual_physical_support_trials"]:
            support = trial["full_support_index"]
            if trial["certificate"] is None:
                if trial["arithmetic_result"] is not None or trial["strict_entire_physical_leaf"] is not False:
                    raise ValueError("expanded failed LDL proposal promoted to exact proof")
                checked.append({"whole_leaf_index":index,"full_support_index":support,
                                "no_exact_LDL_certificate":True,"strict_entire_physical_leaf":False})
                continue
            exact = {"NEW_correlated_quadratic_certificate":trial["certificate"],
                     "NEW_correlated_exact_closed_leaf_result":trial["arithmetic_result"]}
            result = arithmetic.arithmetic_control(original,kernels[support],leaf,exact,arcs)
            weight = F(sum(kernels[support]["weights"]),kernels[support]["scale"])
            if F(result["NEW_full134rod_energy_upper_at_same_root"]) != original["radius"]**2*weight:
                raise ValueError("expanded physical bound used an augmented origin budget")
            strict = result["arithmetic_strict_target_test_passed"]
            if strict != trial["strict_entire_physical_leaf"]:
                raise ValueError("independent expanded whole-bound strict class differs")
            if strict and (F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0):
                raise ValueError("expanded physical bound lacks exact energy AND radius strictness")
            proved |= strict
            checked.append({"whole_leaf_index":index,"full_support_index":support,
                            "strict_entire_physical_leaf":strict,"strict_radius_margin":result["strict_radius_margin"]})
        if target["strict_whole_physical_leaf"] != proved:
            raise ValueError("independent expanded whole-leaf strict subset differs")
        if proved:
            strict_whole.add(index)
        if number % 16 == 0 or number == len(record["actual_current_whole_leaf_trials"]) or not proved:
            print(json.dumps({"independent_expanded_whole_leaf_checks":number,
                              "of":len(record["actual_current_whole_leaf_trials"]),
                              "strict_whole_leaves":len(strict_whole),"last_whole_leaf":index}),flush=True)
    failed = sorted(target["actual_current_whole_OPEN_leaf"]["index"]
                    for target in record["actual_current_whole_leaf_trials"]
                    if target["actual_current_whole_OPEN_leaf"]["index"] not in strict_whole)
    if strict_whole != targets or record["actual_failed_whole_leaf_indices"] != failed:
        raise ValueError("independent expanded physical strict/failed whole sets differ")
    rejected = []

    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid expanded physical batch accepted: "+label)

    reject("arithmetic-promoted-to-global",lambda:scope({**record,"global_optimality_proved":True},args,seed))
    reject("actual-paired530-reset-to-ancestor",lambda:scope({
        **record,"actual_current_seed_sha256":source.earlier.SEED_SHA},args,seed))
    reject("actual-current-count-forged",lambda:scope({
        **record,"actual_current_OPEN_count":args.expected_open+1},args,seed))
    reject("expanded27-table-forged-as-old19",lambda:scope({
        **record,"actual_current_support_count":19},args,seed))
    reject("old-current-retention-denied",lambda:source.ownership({
        **record,"old_current_nodes_supports_and_strict_rows_UNMODIFIED":False},seed,pending))
    trials = record["actual_current_whole_leaf_trials"]
    reject("whole-current-domain-duplicated",lambda:source.ownership({
        **record,"actual_current_whole_leaf_trials":[*trials,trials[0]]},seed,pending))
    changed = deepcopy(trials[0])
    leaf = changed["actual_current_whole_OPEN_leaf"]
    coordinate = next(i for i,(a,b) in enumerate(zip(leaf["lower"],leaf["upper"])) if F(a) < F(b))
    leaf["upper"][coordinate] = str((F(leaf["lower"][coordinate])+F(leaf["upper"][coordinate]))/2)
    reject("proper-subbox-forged-as-whole-current-domain",lambda:source.ownership({
        **record,"actual_current_whole_leaf_trials":[changed,*trials[1:]]},seed,pending))
    changed = deepcopy(trials[0])
    changed["actual_physical_support_trials"][0]["full_support_index"] = args.expected_supports
    reject("support-outside-actual-expanded-table",lambda:source.ownership({
        **record,"actual_current_whole_leaf_trials":[changed,*trials[1:]]},seed,pending))
    reject("immutable-attempt-omitted",lambda:checkpoint_gate({
        **record,"actual_immutable_attempt_checkpoints":record["actual_immutable_attempt_checkpoints"][:-1]}))
    changed = deepcopy(supports[-1]["kernel_certificate"])
    changed["inverse_numerators"][0][0] = str(int(changed["inverse_numerators"][0][0])+1)
    reject("new60ground-inverse-corrupted",lambda:inverse_check.kernel_controls(model,changed))
    changed_mode = deepcopy(supports[-1]["kernel_certificate"])
    changed_mode["mode"] = "ORIGIN-OWNER-AUGMENTED"
    reject("origin-mode-forged-as-physical",lambda:inverse_check.kernel_controls(model,changed_mode))
    for text,digest in {**inventory,**record["input_sha256"],**checkpoints}.items():
        if binding.sha(text) != digest:
            raise ValueError("expanded physical source/checkpoint changed during independent calculations")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("expanded physical diagnosis changed during independent arithmetic")
    inventory.update(record["input_sha256"])
    inventory.update(checkpoints)
    for module in (inverse_check,arithmetic,positive):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_current_support_count":args.expected_supports,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "all_actual_new_whole_physical_bounds_including_failures_independently_recomputed":checked,
        "new_strict_whole_leaf_indices":sorted(strict_whole),"actual_failed_whole_leaf_indices":failed,
        "prospective_remaining_OPEN_after_independent_join":args.expected_open-len(strict_whole),
        "all_old_current_nodes_supports_and_strict_rows_retained":True,
        "all_actual_expanded_physical_inverses_freshly_independently_checked":args.expected_supports,
        "expanded_actual_physical_support_table_reused_unchanged_NO_append":True,
        "known_exact_covering_root_not_excluded_by_any_actual_physical_support":True,
        "no_origin_owner_or_virtual_mu_used_in_NEW_physical_proofs":True,
        "all_actual_immutable_attempt_checkpoints_rechecked":len(checkpoints),
        "actual_source_count_table_subset_mode_inverse_checkpoint_and_retention_rejections":rejected,
        "old_mathematics_explicit_qualified_REUSE_NOT_fresh_all_history_replay":True,
        "current_global_tree_UNMODIFIED_separate_checked_history_join_STILL_required":True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_expanded_physical_batch_completed_NOT_admission":True,
                      "new_strict_whole_leaves":len(strict_whole),"retained_failed_whole_leaves":len(failed),
                      "prospective_OPEN_PENDING_independent_join":args.expected_open-len(strict_whole),
                      "actual_rejection_controls":len(rejected)}),flush=True)


if __name__ == "__main__":
    main()
