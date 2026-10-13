"""Distinct selected physical batches with explicit independently executed actions.

The generic v2 composition FORMAT is reused,not any v2 producer/test receipt.
Every report records this actual executor and action. Old histories are
qualified checked reuse; nothing here is source geometry or global acceptance.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_current_physical_context_v2 as source
import probe_expanded_current_physical_support_reuse_v2 as prior
import test_expanded_current_physical_support_reuse_v2 as prior_test
import n26_preserved_diagonal_strip_refinement_v1 as finer
import probe_joint_remaining_origin25_primal as references
import test_full_candidate_face_energy as inverses
import test_full134rod_correlated_support as independent
import test_latest878_physical_donor_sweep as positive
import verify_conditional_force_stage as binding


PRIMARY = "N26-unaccepted-selected-current-physical-whole-reuse-v1"
CONTROL = "N26-independent-selected-current-physical-whole-reuse-v1"
CHECKPOINT = "N26-unaccepted-selected-current-physical-whole-checkpoint-v1"
FORMAT = "N26-selected-physical-reuse-distinct-executor-actions-v1"
PROOF = Path("work/n26-selected-current-physical-reuse-proof-v1.md")
FALSE_FIELDS = ("global_lower_bound_proved","global_optimality_proved","n27_started")


def unpaid(record):
    if (record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or any(record[field] is not False for field in FALSE_FIELDS)):
        raise ValueError("selected physical evidence promoted to geometry/global completion")


def inventory_gate(inventory):
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("selected physical actual prerequisite changed: "+text)


def method(args):
    return {"selection":args.selection,"parts":args.parts,
            "support_tries":3 if args.selection == "untried" else 1}


def parameters(args,seed,pending):
    if (
        binding.sha(args.parameter_batch) != args.parameter_batch_sha256
        or binding.sha(args.parameter_controls) != args.parameter_controls_sha256
        or seed["input_sha256"].get(linux(args.parameter_batch)) != args.parameter_batch_sha256
        or seed["input_sha256"].get(linux(args.parameter_controls)) != args.parameter_controls_sha256
    ):
        raise ValueError("selected batch parameter pair is not retained by the actual current head")
    old,controls = binding.read(args.parameter_batch),binding.read(args.parameter_controls)
    unpaid(old)
    unpaid(controls)
    if (
        old["schema"] != prior.SCHEMA or controls["schema"] != prior_test.SCHEMA
        or controls["diagnosis_sha256"] != args.parameter_batch_sha256
        or old["source_OPEN_index"] != 25 or controls["source_OPEN_index"] != 25
        or old["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or old["source_file_sha256"] != seed["source_file_sha256"]
        or old["actual_current_support_count"] != args.expected_supports
        or controls["actual_current_support_count"] != args.expected_supports
        or controls["new_strict_whole_leaf_indices"] != old["new_strict_whole_leaf_indices"]
        or controls["actual_failed_whole_leaf_indices"] != old["actual_failed_whole_leaf_indices"]
        or controls["all_actual_expanded_physical_inverses_freshly_independently_checked"] != args.expected_supports
        or controls["expanded_actual_physical_support_table_reused_unchanged_NO_append"] is not True
        or controls["all_actual_immutable_attempt_checkpoints_rechecked"] != len(old["actual_current_whole_leaf_trials"])
        or controls["executed_test_sha256"] != binding.sha(prior_test.__file__)
        or old["executed_producer_sha256"] != binding.sha(prior.__file__)
    ):
        raise ValueError("selected physical parameter data lost actual independent source/table/failure scope")
    by_index = {target["actual_current_whole_OPEN_leaf"]["index"]:target
                for target in old["actual_current_whole_leaf_trials"]}
    if len(by_index) != len(old["actual_current_whole_leaf_trials"]):
        raise ValueError("selected parameter data duplicated an entire source domain")
    current = {leaf["index"]:leaf for leaf in pending}
    for index,target in by_index.items():
        if index in current and current[index] != target["actual_current_whole_OPEN_leaf"]:
            raise ValueError("selected parameter domain was clipped or reset by the current head")
    failed = set(old["actual_failed_whole_leaf_indices"])
    eligible = [leaf for leaf in pending if leaf["index"] in failed] if args.selection == "failed-refine" else [
        leaf for leaf in pending if leaf["index"] not in by_index]
    if args.selection == "failed-refine":
        if args.parts <= old["method_parameters"]["parts"]:
            raise ValueError("failed-refine must genuinely change the Taylor partition")
        def score(leaf):
            trials = by_index[leaf["index"]]["actual_physical_support_trials"]
            values = [F(trial["arithmetic_result"]["strict_radius_margin"]) for trial in trials
                      if trial["certificate"] is not None and trial["arithmetic_result"] is not None]
            return max(values) if values else F(-100)
        eligible.sort(key=score,reverse=True)
    return old,controls,by_index,eligible


def inputs(args):
    values = source.inputs(args)
    original,model,seed,controls,row,pending,supports,kernels,turns,arcs,inventory = values
    old,old_controls,previous,eligible = parameters(args,seed,pending)
    for record in (old,old_controls):
        inventory_gate(record["input_sha256"])
        for text,digest in record["input_sha256"].items():
            if text in inventory and inventory[text] != digest:
                raise ValueError("selected actual current/parameter digest conflict")
            inventory[text] = digest
    for module in (finer,finer.exact,finer.numerical,references,inverses,independent,positive):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({
        linux(args.parameter_batch):args.parameter_batch_sha256,
        linux(args.parameter_controls):args.parameter_controls_sha256,
        linux(PROOF):binding.sha(PROOF),linux(__file__):binding.sha(__file__),
    })
    return values,old,previous,eligible,inventory


def scope(record,args,seed,pending,eligible):
    unpaid(record)
    if (
        record["schema"] != PRIMARY or record["source_OPEN_index"] != 25
        or record["actual_current_seed_file"] != linux(args.seed)
        or record["actual_current_seed_sha256"] != args.seed_sha256
        or record["actual_current_controls_file"] != linux(args.seed_controls)
        or record["actual_current_controls_sha256"] != args.seed_controls_sha256
        or record["actual_current_OPEN_count"] != args.expected_open
        or record["actual_current_support_count"] != args.expected_supports
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["parameter_batch_sha256"] != args.parameter_batch_sha256
        or record["parameter_controls_sha256"] != args.parameter_controls_sha256
        or record["method_parameters"] != method(args)
        or record["all_eligible_whole_leaf_indices"] != sorted(leaf["index"] for leaf in eligible)
        or record["expanded_actual_physical_support_table_reused_unchanged_NO_append"] is not True
        or record["executed_action"] != "primary"
        or record["executed_producer_sha256"] != binding.sha(__file__)
    ):
        raise ValueError("selected batch changed actual parent,selection,table,method or executor/action")
    indices = [target["actual_current_whole_OPEN_leaf"]["index"]
               for target in record["actual_current_whole_leaf_trials"]]
    if not indices or not set(indices) <= {leaf["index"] for leaf in eligible}:
        raise ValueError("selected batch attempted a repeated failure or another source domain")
    for target in record["actual_current_whole_leaf_trials"]:
        attempts = target["actual_physical_support_trials"]
        owners = [trial["full_support_index"] for trial in attempts]
        if not 1 <= len(attempts) <= method(args)["support_tries"] or len(set(owners)) != len(owners):
            raise ValueError("selected batch duplicated a support or changed actual attempt budget")
        for trial in target["actual_physical_support_trials"]:
            if trial["certificate"] is not None and trial["certificate"]["parts"] != args.parts:
                raise ValueError("selected batch reused an unchanged or relabelled old partition")
    return source.ownership(record,seed,pending)


def checkpoints(record):
    trials = record["actual_current_whole_leaf_trials"]
    actual = {item["actual_current_whole_OPEN_leaf"]["index"]:item for item in trials}
    seen,inventory = set(),{}
    for item in record["actual_immutable_attempt_checkpoints"]:
        index = item["whole_leaf_index"]
        if index in seen or index not in actual or binding.sha(item["path"]) != item["sha256"]:
            raise ValueError("selected physical checkpoint repeated,omitted or changed")
        seen.add(index)
        point = binding.read(item["path"])
        if (
            point["schema"] != CHECKPOINT or point["actual_current_seed_sha256"] != record["actual_current_seed_sha256"]
            or point["actual_whole_leaf_trial"] != actual[index]
            or point["executed_producer_sha256"] != record["executed_producer_sha256"]
            or point["executed_action"] != "primary" or point["verified"] is not False
            or point["new_geometric_payments"] != 0 or point["global_optimality_proved"] is not False
        ):
            raise ValueError("selected checkpoint changed an actual entire-domain proof/failed trial")
        inventory[item["path"]] = item["sha256"]
    if len(actual) != len(trials) or seen != set(actual):
        raise ValueError("selected physical attempted domain has no unique checkpoint")
    return inventory


def write(args,record):
    if args.report.exists():
        raise FileExistsError("preserve selected physical completed/failed evidence")
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(record,indent=2)+"\n")


def primary(args):
    if args.report.exists() or args.checkpoint_directory.exists():
        raise FileExistsError("fresh selected primary and checkpoint paths required")
    values,old,previous,eligible,inventory = inputs(args)
    original,model,seed,controls,row,pending,supports,kernels,turns,arcs,_ = values
    if not 1 <= args.limit <= len(eligible):
        raise ValueError("selected primary limit exceeds the actual eligible whole-domain inventory")
    if args.selection == "untried":
        ranks = source.INITIAL.rank_leaves(original,kernels,eligible)
        lookup = {leaf["index"]:leaf for leaf in eligible}
        selected = [lookup[item["actual_OPEN_leaf_index"]] for item in ranks[:args.limit]]
        choices = {item["actual_OPEN_leaf_index"]:item["suggested_existing_full_support_index"] for item in ranks}
        prepared = [
            (np.array([i for i,j,w in kernel["pairs"]]),np.array([j for i,j,w in kernel["pairs"]]),
             np.array([float(F(w,kernel["inverse_denominator"]*sum(kernel["weights"]))) for i,j,w in kernel["pairs"]]))
            for kernel in kernels
        ]
    else:
        selected = eligible[:args.limit]
    args.checkpoint_directory.mkdir(parents=False)
    results,succeeded,failed,saved = [],[],[],[]
    print(json.dumps({"actual_selected_current_source_reconstructed":True,"current_OPEN":len(pending),
                      "eligible_whole_domains":len(eligible),"selection":args.selection,"actual_limit":args.limit}),flush=True)
    for number,leaf in enumerate(selected,1):
        index = leaf["index"]
        if args.selection == "failed-refine":
            previous_trials = previous[index]["actual_physical_support_trials"]
            usable = [trial for trial in previous_trials if trial["certificate"] is not None
                      and trial["arithmetic_result"] is not None]
            if usable:
                parameter = max(usable,key=lambda trial:F(trial["arithmetic_result"]["strict_radius_margin"]))
                support = parameter["full_support_index"]
                certificate,result,suggestions = finer.suggest(
                    kernels[support],original["matrix"],leaf["lower"],leaf["upper"],
                    parameter["certificate"],original["radius"],arcs,args.parts)
            else:
                support = previous_trials[0]["full_support_index"]
                ref,_ = references.exact_turns(original,leaf,turns[support])
                certificate,result,suggestions = source.earlier.suggestion.suggest(
                    kernels[support],original["matrix"],leaf["lower"],leaf["upper"],ref,original["radius"],arcs,args.parts)
            strict = bool(result is not None and result["arithmetic_strict_target_test_passed"] is True)
            trial = {"full_support_index":support,"certificate":certificate,"arithmetic_result":result,
                     "strict_entire_physical_leaf":strict,"numerical_suggestions_NOT_proof":suggestions}
            trials,selected_proof = [trial],trial if strict else None
        else:
            middle = np.array([0.,*[float((F(a)+F(b))/2) for a,b in zip(leaf["lower"],leaf["upper"])]])
            scores = sorted([(float(2*(1-np.cos(2*np.pi*(middle[right]-middle[left])))@weights),i)
                             for i,(left,right,weights) in enumerate(prepared)],reverse=True)
            first = choices[index]
            best_new = next(i for value,i in scores if i >= 19)
            order = list(dict.fromkeys([first,best_new,*[i for value,i in scores]]))[:3]
            trials,selected_proof = [],None
            for support in order:
                ref,_ = references.exact_turns(original,leaf,turns[support])
                certificate,result,suggestions = source.earlier.suggestion.suggest(
                    kernels[support],original["matrix"],leaf["lower"],leaf["upper"],ref,original["radius"],arcs,args.parts)
                strict = bool(result is not None and result["arithmetic_strict_target_test_passed"] is True)
                trial = {"full_support_index":support,"certificate":certificate,"arithmetic_result":result,
                         "strict_entire_physical_leaf":strict,"numerical_suggestions_NOT_proof":suggestions}
                trials.append(trial)
                if strict:
                    selected_proof = trial
                    break
            strict = selected_proof is not None
        item = {"actual_current_whole_OPEN_leaf":leaf,"actual_physical_support_trials":trials,
                "selected_strict_physical_proof":selected_proof,"strict_whole_physical_leaf":strict}
        results.append(item)
        (succeeded if strict else failed).append(index)
        path = args.checkpoint_directory/f"leaf-{index:05d}.json"
        with path.open("x",encoding="utf-8",newline="\n") as output:
            output.write(json.dumps({
                "schema":CHECKPOINT,"verified":False,"actual_current_seed_sha256":args.seed_sha256,
                "actual_whole_leaf_trial":item,"executed_producer_sha256":binding.sha(__file__),
                "executed_action":"primary","new_geometric_payments":0,"global_optimality_proved":False,
            },indent=2)+"\n")
        saved.append({"whole_leaf_index":index,"path":linux(path),"sha256":binding.sha(path)})
        if number % 8 == 0 or number == args.limit or strict:
            print(json.dumps({"selected_physical_whole_attempts":number,"of":args.limit,
                              "new_strict_whole_leaves":len(succeeded),"retained_failures":len(failed),
                              "last_whole_leaf":index,"last_strict":strict}),flush=True)
    record = {
        "schema":PRIMARY,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_current_support_count":args.expected_supports,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "parameter_batch_sha256":args.parameter_batch_sha256,"parameter_controls_sha256":args.parameter_controls_sha256,
        "method_parameters":method(args),
        "all_eligible_whole_leaf_indices":sorted(leaf["index"] for leaf in eligible),
        "actual_current_whole_leaf_trials":results,"actual_immutable_attempt_checkpoints":saved,
        "new_strict_whole_leaf_indices":sorted(succeeded),"actual_failed_whole_leaf_indices":sorted(failed),
        "prospective_remaining_OPEN_after_independent_join":len(pending)-len(succeeded),
        "old_current_nodes_supports_and_strict_rows_UNMODIFIED":True,
        "expanded_actual_physical_support_table_reused_unchanged_NO_append":True,
        "old_mathematics_explicit_qualified_REUSE_NOT_fresh_all_history_replay":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),"executed_action":"primary",
    }
    scope(record,args,seed,pending,eligible)
    inventory_gate(inventory)
    write(args,record)
    print(json.dumps({"selected_primary_complete_NOT_admission":True,"strict_whole_leaves":len(succeeded),
                      "prospective_OPEN_PENDING_independent_join":len(pending)-len(succeeded)}),flush=True)


def check(args):
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual exact completed selected primary required")
    values,old,previous,eligible,inventory = inputs(args)
    original,model,seed,controls,row,pending,supports,kernels,turns,arcs,_ = values
    record = binding.read(args.diagnosis)
    inventory_gate(record["input_sha256"])
    strict = scope(record,args,seed,pending,eligible)
    points = checkpoints(record)
    for i,support in enumerate(supports):
        kernel,identity = inverses.kernel_controls(model,support["kernel_certificate"])
        if kernel != kernels[i] or not positive.root_positive(original,kernel):
            raise ValueError("selected independent physical inverse or known root check failed")
    domains,parents = source.domains.all_domains(original,row,seed["nodes"])
    rows,independently_strict = [],set()
    for number,target in enumerate(record["actual_current_whole_leaf_trials"],1):
        leaf = target["actual_current_whole_OPEN_leaf"]
        if domains[leaf["index"]] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("selected independent whole source domain differs")
        success = False
        for trial in target["actual_physical_support_trials"]:
            support = trial["full_support_index"]
            result = None
            if trial["certificate"] is not None:
                result = independent.arithmetic_control(original,kernels[support],leaf,{
                    "NEW_correlated_quadratic_certificate":trial["certificate"],
                    "NEW_correlated_exact_closed_leaf_result":trial["arithmetic_result"]},arcs)
                weight = F(sum(kernels[support]["weights"]),kernels[support]["scale"])
                if F(result["NEW_full134rod_energy_upper_at_same_root"]) != original["radius"]**2*weight:
                    raise ValueError("selected physical proof used a virtual origin budget")
            elif trial["arithmetic_result"] is not None:
                raise ValueError("selected failed LDL proposal has a forged exact result")
            proved = bool(result is not None and result["arithmetic_strict_target_test_passed"] is True)
            if proved != trial["strict_entire_physical_leaf"]:
                raise ValueError("selected independent strict/failed classification differs")
            success |= proved
            rows.append({"whole_leaf_index":leaf["index"],"full_support_index":support,
                         "strict_entire_physical_leaf":proved,
                         "strict_radius_margin":result["strict_radius_margin"] if result else None})
        if success:
            independently_strict.add(leaf["index"])
        if number % 8 == 0 or number == len(record["actual_current_whole_leaf_trials"]) or success:
            print(json.dumps({"independent_selected_whole_checks":number,
                              "strict_whole_leaves":len(independently_strict),"last_whole_leaf":leaf["index"]}),flush=True)
    failed = sorted(target["actual_current_whole_OPEN_leaf"]["index"] for target in record["actual_current_whole_leaf_trials"]
                    if target["actual_current_whole_OPEN_leaf"]["index"] not in independently_strict)
    if strict != independently_strict or failed != record["actual_failed_whole_leaf_indices"]:
        raise ValueError("selected independent strict/failed entire-domain sets differ")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid selected physical control accepted: "+label)
    reject("arithmetic-promoted-to-global",lambda:scope({**record,"global_optimality_proved":True},args,seed,pending,eligible))
    reject("different-selected-method",lambda:scope({**record,"method_parameters":{}},args,seed,pending,eligible))
    reject("current-parent-reset",lambda:scope({**record,"actual_current_seed_sha256":"0"*64},args,seed,pending,eligible))
    trials = record["actual_current_whole_leaf_trials"]
    reject("whole-domain-duplicated",lambda:scope({
        **record,"actual_current_whole_leaf_trials":[*trials,trials[0]]},args,seed,pending,eligible))
    bad = deepcopy(trials[0])
    leaf = bad["actual_current_whole_OPEN_leaf"]
    axis = next(i for i,(a,b) in enumerate(zip(leaf["lower"],leaf["upper"])) if F(a) < F(b))
    leaf["upper"][axis] = str((F(leaf["lower"][axis])+F(leaf["upper"][axis]))/2)
    reject("proper-subbox-forged-whole",lambda:scope({
        **record,"actual_current_whole_leaf_trials":[bad,*trials[1:]]},args,seed,pending,eligible))
    reject("checkpoint-omitted",lambda:checkpoints({
        **record,"actual_immutable_attempt_checkpoints":record["actual_immutable_attempt_checkpoints"][:-1]}))
    inventory.update(record["input_sha256"])
    inventory.update(points)
    inventory[linux(args.diagnosis)] = args.diagnosis_sha256
    inventory_gate(inventory)
    write(args,{
        "schema":CONTROL,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_current_seed_sha256":args.seed_sha256,"actual_current_controls_sha256":args.seed_controls_sha256,
        "method_parameters":record["method_parameters"],"actual_current_support_count":args.expected_supports,
        "new_strict_whole_leaf_indices":sorted(strict),"actual_failed_whole_leaf_indices":failed,
        "all_actual_whole_bounds_including_failures_independently_recomputed":rows,
        "all_current_physical_inverses_freshly_independently_checked":args.expected_supports,
        "all_actual_checkpoints_rechecked":len(points),"actual_rejection_controls":rejected,
        "arithmetic_only_NOT_latest_geometry_or_global_acceptance":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),"executed_action":"check",
    })
    print(json.dumps({"independent_selected_math_complete_NOT_admission":True,"strict_whole_leaves":len(strict),
                      "retained_failures":len(failed),"actual_rejections":len(rejected)}),flush=True)


def join_inputs(args):
    seed,old_controls,inventory = source.paired(args)
    old,old_control,previous,eligible = parameters(args,seed,seed["pending_closed_leaf_boxes"])
    if binding.sha(args.batch) != args.batch_sha256 or binding.sha(args.batch_controls) != args.batch_controls_sha256:
        raise ValueError("actual completed selected batch/control pair required before join")
    batch,controls = binding.read(args.batch),binding.read(args.batch_controls)
    strict = scope(batch,args,seed,seed["pending_closed_leaf_boxes"],eligible)
    point_inventory = checkpoints(batch)
    unpaid(controls)
    if (
        controls["schema"] != CONTROL or controls["diagnosis_sha256"] != args.batch_sha256
        or controls["actual_current_seed_sha256"] != args.seed_sha256
        or controls["actual_current_controls_sha256"] != args.seed_controls_sha256
        or controls["method_parameters"] != batch["method_parameters"]
        or controls["actual_current_support_count"] != args.expected_supports
        or controls["new_strict_whole_leaf_indices"] != sorted(strict)
        or controls["actual_failed_whole_leaf_indices"] != batch["actual_failed_whole_leaf_indices"]
        or controls["all_current_physical_inverses_freshly_independently_checked"] != args.expected_supports
        or controls["all_actual_checkpoints_rechecked"] != len(point_inventory)
        or controls["executed_test_sha256"] != binding.sha(__file__) or controls["executed_action"] != "check"
    ):
        raise ValueError("selected join lost actual independent table,whole-bound or action scope")
    checked = {(item["whole_leaf_index"],item["full_support_index"]):item
               for item in controls["all_actual_whole_bounds_including_failures_independently_recomputed"]}
    attempted = {(target["actual_current_whole_OPEN_leaf"]["index"],trial["full_support_index"])
                 for target in batch["actual_current_whole_leaf_trials"] for trial in target["actual_physical_support_trials"]}
    if set(checked) != attempted or len(checked) != len(controls["all_actual_whole_bounds_including_failures_independently_recomputed"]):
        raise ValueError("selected join omitted/duplicated an actual independent attempt")
    for target in batch["actual_current_whole_leaf_trials"]:
        index = target["actual_current_whole_OPEN_leaf"]["index"]
        for trial in target["actual_physical_support_trials"]:
            item = checked[index,trial["full_support_index"]]
            if item["strict_entire_physical_leaf"] != trial["strict_entire_physical_leaf"]:
                raise ValueError("selected join changed an actual independent failed/strict class")
        if index in strict:
            proof = target["selected_strict_physical_proof"]
            if F(checked[index,proof["full_support_index"]]["strict_radius_margin"]) <= 0:
                raise ValueError("selected join adopted a nonstrict whole bound")
    for record in (batch,controls):
        inventory_gate(record["input_sha256"])
        for text,digest in record["input_sha256"].items():
            if text in inventory and inventory[text] != digest:
                raise ValueError("selected join prerequisite conflict")
            inventory[text] = digest
    inventory.update(point_inventory)
    inventory.update({linux(args.batch):args.batch_sha256,linux(args.batch_controls):args.batch_controls_sha256,
                      linux(__file__):binding.sha(__file__)})
    return seed,batch,controls,strict,inventory


def compose(args):
    seed,batch,controls,strict,inventory = join_inputs(args)
    if not strict:
        raise ValueError("zero newly checked whole exclusions do not advance the arithmetic history")
    nodes,ledger = list(seed["nodes"]),list(seed["arithmetic_ledger"])
    for target in batch["actual_current_whole_leaf_trials"]:
        leaf,proof = target["actual_current_whole_OPEN_leaf"],target["selected_strict_physical_proof"]
        if leaf["index"] in strict:
            node = {"kind":source.MIXED.KIND,"full_support_index":proof["full_support_index"],"certificate":proof["certificate"]}
            nodes[leaf["index"]] = node
            ledger.append({**leaf,**node,"arithmetic_result":proof["arithmetic_result"]})
    ledger.sort(key=lambda leaf:leaf["index"])
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    payload = {"nodes":nodes,"arithmetic_ledger":ledger,"alternative_supports":seed["alternative_supports"],
               "full134rod_supports":seed["full134rod_supports"]}
    retained = source.MIXED.retention_gate(seed,payload)
    inventory_gate(inventory)
    write(args,{
        "schema":source.REUSE_SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_distinct_executor_format":FORMAT,"executed_action":"compose",
        "actual_source_closed_box":seed["actual_source_closed_box"],"source_file_sha256":seed["source_file_sha256"],
        "actual_current_predecessor_file":linux(args.seed),"actual_current_predecessor_sha256":args.seed_sha256,
        "actual_current_predecessor_controls_file":linux(args.seed_controls),
        "actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "actual_complete_physical_reuse_batch_file":linux(args.batch),"actual_complete_physical_reuse_batch_sha256":args.batch_sha256,
        "actual_complete_physical_reuse_controls_file":linux(args.batch_controls),
        "actual_complete_physical_reuse_controls_sha256":args.batch_controls_sha256,
        "new_whole_actual_current_OPEN_leaf_indices":sorted(strict),**payload,
        "fresh_joint_origin_supports":seed["fresh_joint_origin_supports"],
        "pending_closed_leaf_boxes":pending,"remaining_OPEN_leaf_count":len(pending),
        "total_whole_original_v4_OPEN_leaves_excluded":984-len(pending),"actual_current_support_count":args.expected_supports,
        "retained_old_current_nodes_supports_and_strict_rows":list(retained),
        "expanded_actual_physical_support_table_reused_unchanged_NO_append":True,
        "all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained":True,
        "retained_failed_CURRENT_whole_leaf_indices":batch["actual_failed_whole_leaf_indices"],
        "actual_attempt_method_parameters":batch["method_parameters"],
        "generic_v2_composition_FORMAT_only_NO_v2_executor_or_control_metadata_forged":True,
        "old_ANDnew_mathematics_explicit_qualified_checked_REUSE_NOT_full_replay":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    })
    print(json.dumps({"selected_arithmetic_composition_complete_NOT_admission":True,
                      "new_whole_exclusions":len(strict),"remaining_OPEN":len(pending)}),flush=True)


def retain(record,args,seed,batch,strict):
    unpaid(record)
    if (
        record["schema"] != source.REUSE_SCHEMA or record["actual_distinct_executor_format"] != FORMAT
        or record["executed_action"] != "compose" or record["executed_producer_sha256"] != binding.sha(__file__)
        or record["source_OPEN_index"] != 25 or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_current_predecessor_file"] != linux(args.seed)
        or record["actual_current_predecessor_sha256"] != args.seed_sha256
        or record["actual_current_predecessor_controls_file"] != linux(args.seed_controls)
        or record["actual_current_predecessor_controls_sha256"] != args.seed_controls_sha256
        or record["actual_complete_physical_reuse_batch_file"] != linux(args.batch)
        or record["actual_complete_physical_reuse_batch_sha256"] != args.batch_sha256
        or record["actual_complete_physical_reuse_controls_file"] != linux(args.batch_controls)
        or record["actual_complete_physical_reuse_controls_sha256"] != args.batch_controls_sha256
        or record["new_whole_actual_current_OPEN_leaf_indices"] != sorted(strict)
        or record["full134rod_supports"] != seed["full134rod_supports"]
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["fresh_joint_origin_supports"] != seed["fresh_joint_origin_supports"]
        or len(record["nodes"]) != len(seed["nodes"])
        or any(record["nodes"][i] != node for i,node in enumerate(seed["nodes"]) if i not in strict)
    ):
        raise ValueError("selected independent retention changed parent,mode,node or support/history")
    old = {leaf["index"]:leaf for leaf in seed["arithmetic_ledger"]}
    new = {leaf["index"]:leaf for leaf in record["arithmetic_ledger"]}
    if (len(new) != len(record["arithmetic_ledger"]) or len(new) != len(old)+len(strict)
            or set(new)-set(old) != strict or any(new.get(i) != leaf for i,leaf in old.items())):
        raise ValueError("selected independent retention lost an old row or changed actual payment ownership")
    for target in batch["actual_current_whole_leaf_trials"]:
        leaf,proof = target["actual_current_whole_OPEN_leaf"],target["selected_strict_physical_proof"]
        index = leaf["index"]
        if index in strict:
            node = {"kind":source.MIXED.KIND,"full_support_index":proof["full_support_index"],"certificate":proof["certificate"]}
            if seed["nodes"][index] != {"kind":"OPEN"} or record["nodes"][index] != node or new[index] != {
                    **leaf,**node,"arithmetic_result":proof["arithmetic_result"]}:
                raise ValueError("selected independent retention re-paid,clipped or changed a new entire proof")
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        record["pending_closed_leaf_boxes"] != pending or record["remaining_OPEN_leaf_count"] != len(pending)
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 984-len(pending)
        or record["actual_current_support_count"] != args.expected_supports
        or record["retained_failed_CURRENT_whole_leaf_indices"] != batch["actual_failed_whole_leaf_indices"]
        or record["actual_attempt_method_parameters"] != batch["method_parameters"]
        or record["retained_old_current_nodes_supports_and_strict_rows"] != [
            len(seed["nodes"]),len(seed["alternative_supports"]),len(seed["arithmetic_ledger"])]
    ):
        raise ValueError("selected independent retention lost failed/unselected whole regions")


def final(args):
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual exact completed selected composition required")
    seed,batch,controls,strict,inventory = join_inputs(args)
    record = binding.read(args.diagnosis)
    retain(record,args,seed,batch,strict)
    rejected = []
    def reject(label,bad):
        try:
            retain(bad,args,seed,batch,strict)
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid selected history accepted: "+label)
    reject("promoted-to-global",{**record,"global_optimality_proved":True})
    reject("old-strict-row-omitted",{**record,"arithmetic_ledger":record["arithmetic_ledger"][1:]})
    reject("support-appended",{**record,"full134rod_supports":[*record["full134rod_supports"],record["full134rod_supports"][-1]]})
    nodes = list(record["nodes"])
    nodes[2641] = {"kind":"OPEN"}
    reject("complete-origin-forest-reset",{**record,"nodes":nodes})
    if record["pending_closed_leaf_boxes"]:
        reject("unpaid-domain-omitted",{**record,"pending_closed_leaf_boxes":record["pending_closed_leaf_boxes"][:-1]})
    if strict:
        nodes = list(record["nodes"])
        nodes[min(strict)] = {**nodes[min(strict)],"full_support_index":-1}
        reject("new-support-owner-forged",{**record,"nodes":nodes})
    inventory.update(record["input_sha256"])
    inventory[linux(args.diagnosis)] = args.diagnosis_sha256
    inventory_gate(inventory)
    write(args,{
        "schema":source.REUSE_CONTROL,"verified":False,"source_OPEN_index":25,"diagnosis_sha256":args.diagnosis_sha256,
        "actual_distinct_executor_format":FORMAT,"executed_action":"final",
        "actual_current_predecessor_sha256":args.seed_sha256,"actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "new_whole_actual_current_OPEN_leaf_indices":sorted(strict),
        "remaining_OPEN_leaf_count":args.expected_open-len(strict),
        "total_whole_original_v4_OPEN_leaves_excluded":984-args.expected_open+len(strict),
        "actual_current_support_count":args.expected_supports,
        "all_old_current_nodes_supports_and_strict_rows_retained":True,
        "expanded_actual_physical_support_table_reused_unchanged_NO_append":True,
        "all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained":True,
        "retained_failed_CURRENT_whole_leaf_indices":batch["actual_failed_whole_leaf_indices"],
        "old_ANDnew_math_qualified_checked_REUSE_NOT_fresh_all_history_replay":True,
        "arithmetic_history_only_NOT_latest_geometry_or_global_acceptance":True,"actual_rejection_controls":rejected,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    })
    print(json.dumps({"independent_selected_history_complete_NOT_admission":True,"new_whole_exclusions":len(strict),
                      "remaining_OPEN":args.expected_open-len(strict),"actual_rejections":len(rejected)}),flush=True)


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--action",choices=("primary","check","compose","final"),required=True)
    parser.add_argument("--selection",choices=("failed-refine","untried"),required=True)
    parser.add_argument("--parts",type=int,required=True)
    parser.add_argument("--parameter-batch",type=Path,required=True)
    parser.add_argument("--parameter-batch-sha256",required=True)
    parser.add_argument("--parameter-controls",type=Path,required=True)
    parser.add_argument("--parameter-controls-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--checkpoint-directory",type=Path)
    parser.add_argument("--limit",type=int)
    parser.add_argument("--diagnosis",type=Path)
    parser.add_argument("--diagnosis-sha256")
    parser.add_argument("--batch",type=Path)
    parser.add_argument("--batch-sha256")
    parser.add_argument("--batch-controls",type=Path)
    parser.add_argument("--batch-controls-sha256")
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.parts <= 64:
        raise ValueError("fresh selected output and bounded Taylor strips required")
    if args.action == "primary" and (args.checkpoint_directory is None or args.limit is None):
        raise ValueError("actual primary checkpoint directory and limit required")
    if args.action in ("check","final") and (args.diagnosis is None or args.diagnosis_sha256 is None):
        raise ValueError("actual completed diagnosis/hash required")
    if args.action in ("compose","final") and any(getattr(args,name) is None for name in
                                                ("batch","batch_sha256","batch_controls","batch_controls_sha256")):
        raise ValueError("actual checked batch/control pair required")
    {"primary":primary,"check":check,"compose":compose,"final":final}[args.action](args)


if __name__ == "__main__":
    main()
