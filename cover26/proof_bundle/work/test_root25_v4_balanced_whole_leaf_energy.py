"""Independent new whole-leaf arithmetic and immutable actual v4 retention.

Old516 strict leaf mathematics is explicitly qualified prior checked reuse,
NOT a fresh replay. All NEW full-leaf witnesses are independently recomputed.
No current source or global geometry payment is made.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_root25_v4_balanced_whole_leaf_energy as producer
import test_checked_root28_full134rod_intersections as independent_domains
import test_full134rod_correlated_support as independent_energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-root25v4-width-balanced-whole-leaf-energy-controls-v1"


def scope(record,seed,row):
    if (
        record["schema"] != producer.SCHEMA
        or record["source_OPEN_index"] != 25 or record["actual_source_closed_box"] != row
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_seed_v4_sha256"] != producer.SEED_SHA
        or record["actual_seed_v4_controls_sha256"] != producer.CONTROL_SHA
        or record["actual_proof_time_current_sha256"] != producer.CURRENT_SHA
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in (
            "global_lower_bound_proved","global_optimality_proved","n27_started"))
        or record["unchanged_old_v4_arithmetic_explicitly_REUSED_NOT_a_fresh_all_old_leaf_replay"] is not True
    ):
        raise ValueError("balanced leaf controls changed actual v4/source/unpaid/qualified-reuse scope")


def ownership(record,seed,pending):
    by_index = {leaf["index"]:leaf for leaf in pending}
    targets = record["new_exact_strict_whole_old_OPEN_leaves"]
    seen = set()
    expected_nodes = deepcopy(seed["nodes"])
    expected_ledger = deepcopy(seed["arithmetic_ledger"])
    for target in targets:
        leaf = target["actual_seed_v4_OPEN_leaf"]
        index = leaf["index"]
        if index in seen or by_index.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"}:
            raise ValueError("balanced leaf target duplicated/changed a whole actual v4 OPEN owner")
        seen.add(index)
        support = target["full_support_index"]
        if type(support) is not int or not 0 <= support < len(seed["full134rod_supports"]):
            raise ValueError("balanced target names an unbound original full134rod support")
        expected_nodes[index] = {
            "kind":producer.mixed.KIND,"full_support_index":support,"certificate":target["certificate"]}
        expected_ledger.append({**leaf,"kind":producer.mixed.KIND,"full_support_index":support,
                                "certificate":target["certificate"],"arithmetic_result":target["arithmetic_result"]})
    expected_ledger.sort(key=lambda row:row["index"])
    expected_pending = [leaf for leaf in pending if leaf["index"] not in seen]
    if (
        record["nodes"] != expected_nodes or record["arithmetic_ledger"] != expected_ledger
        or record["pending_closed_leaf_boxes"] != expected_pending
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["full134rod_supports"] != seed["full134rod_supports"]
        or record["new_exact_strict_whole_old_OPEN_leaf_count"] != len(seen)
        or record["remaining_OPEN_leaf_count"] != len(expected_pending)
        or len(expected_pending)+len(seen) != 984
    ):
        raise ValueError("balanced whole-leaf continuation changed old proof or lost unpaid domains")
    return targets,expected_pending


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh independent report/exact completed balanced diagnosis required")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("actual balanced diagnostic prerequisite changed")
    original,model,kernels,seed,seed_controls,row,pending,arcs,inventory = producer.source_inputs()
    scope(record,seed,row)
    targets,remaining = ownership(record,seed,pending)
    retained = producer.mixed.retention_gate(seed,record)
    if record["immutable_v4_node_support_and_strict_ledger_retention_counts"] != list(retained):
        raise ValueError("independent exact old516-ledger/node/support retention differs")
    before,parents = independent_domains.all_domains(original,row,seed["nodes"])
    after,after_parents = independent_domains.all_domains(original,row,record["nodes"])
    if before != after or parents != after_parents:
        raise ValueError("new whole-leaf payments changed any old actual closed domain or shared boundary")
    checked,margins = [],[]
    for number,target in enumerate(targets,1):
        leaf,support = target["actual_seed_v4_OPEN_leaf"],target["full_support_index"]
        if before[leaf["index"]] != (list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("whole target bounds are not the independent entire actual source leaf")
        trial = {"NEW_correlated_quadratic_certificate":target["certificate"],
                 "NEW_correlated_exact_closed_leaf_result":target["arithmetic_result"]}
        result = independent_energy.arithmetic_control(original,kernels[support],leaf,trial,arcs)
        if (
            result["arithmetic_strict_target_test_passed"] is not True
            or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
        ):
            raise ValueError("independent whole-leaf arithmetic failed strict energy/radius")
        margins.append(F(result["strict_radius_margin"]))
        checked.append({"actual_seed_v4_OPEN_leaf_index":leaf["index"],"full_support_index":support,
                        "strict_radius_margin":result["strict_radius_margin"]})
        print(json.dumps({"independent_actual_whole_OPEN_leaf_energy":number,"of":len(targets),
                          "old_v4_leaf_index":leaf["index"],"strict":True}),flush=True)
    # All actual attempted results (including failed ones) retain their exact
    # leaf owner, and the strict subset equals the advertised payments.
    attempted,strict_attempts = set(),set()
    by_index = {leaf["index"]:leaf for leaf in pending}
    for item in record["actual_entire_leaf_energy_trials"]:
        leaf = item["actual_latest_v4_whole_OPEN_leaf"]
        index = leaf["index"]
        if index in attempted or by_index.get(index) != leaf:
            raise ValueError("actual whole-leaf attempt list changed source ownership")
        attempted.add(index)
        strict = any(trial["exact_whole_leaf_result"] is not None
                     and trial["exact_whole_leaf_result"]["arithmetic_strict_target_test_passed"] is True
                     for trial in item["trials"])
        if strict != item["fresh_exact_entire_OPEN_leaf_strict"]:
            raise ValueError("actual attempted strict classification changed")
        if strict:
            strict_attempts.add(index)
    if strict_attempts != {row["actual_seed_v4_OPEN_leaf"]["index"] for row in targets}:
        raise ValueError("independent target set differs from all actual strict attempts")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid balanced whole-leaf control accepted: "+label)
    changed = {**record,"global_optimality_proved":True}
    reject("arithmetic-promoted-to-global-proof",lambda:scope(changed,seed,row))
    changed = deepcopy(record)
    changed["pending_closed_leaf_boxes"].pop()
    reject("lost-unselected-or-failed-OPEN-leaf",lambda:ownership(changed,seed,pending))
    changed = deepcopy(record)
    changed["nodes"][next(i for i,node in enumerate(seed["nodes"]) if node["kind"] != "OPEN")] = {"kind":"OPEN"}
    reject("old-nonOPEN-proof-reset",lambda:ownership(changed,seed,pending))
    changed = deepcopy(record)
    changed["arithmetic_ledger"].pop(0)
    reject("old-strict-ledger-row-omitted",lambda:ownership(changed,seed,pending))
    changed = deepcopy(record)
    changed["full134rod_supports"].pop()
    reject("old-positive-support-prefix-truncated",lambda:ownership(changed,seed,pending))
    if targets:
        changed = deepcopy(record)
        changed["new_exact_strict_whole_old_OPEN_leaves"].append(deepcopy(targets[0]))
        reject("duplicate-entire-OPEN-payment",lambda:ownership(changed,seed,pending))
        changed = deepcopy(record)
        leaf = changed["new_exact_strict_whole_old_OPEN_leaves"][0]["actual_seed_v4_OPEN_leaf"]
        leaf["lower"][0] = str((F(leaf["lower"][0])+F(leaf["upper"][0]))/2)
        reject("proper-subbox-relabelled-as-whole-old-leaf",lambda:ownership(changed,seed,pending))
        changed = deepcopy(record)
        changed["new_exact_strict_whole_old_OPEN_leaves"][0]["full_support_index"] = -1
        reject("wrong-full134-support-owner",lambda:ownership(changed,seed,pending))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("balanced whole-leaf evidence changed during independent controls")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("balanced primary diagnosis changed during independent controls")
    inventory.update({
        linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__),
        linux(independent_energy.__file__):binding.sha(independent_energy.__file__),
        linux(independent_domains.__file__):binding.sha(independent_domains.__file__),
    })
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_source_closed_box":row,
        "source_file_sha256":seed["source_file_sha256"],"diagnosis_sha256":args.diagnosis_sha256,
        "actual_original_v4_seed_sha256":producer.SEED_SHA,
        "actual_original_v4_controls_sha256":producer.CONTROL_SHA,
        "all_old2999_domains_and_shared_boundaries_independently_unchanged":True,
        "all_old_nodes_supports_AND516_strict_ledger_rows_retained":list(retained),
        "all_NEW_actual_entire_old_OPEN_energy_witnesses_independently_recomputed":checked,
        "new_strict_whole_old_OPEN_leaf_count":len(checked),"remaining_OPEN_leaf_count":len(remaining),
        "minimum_NEW_strict_radius_margin":str(min(margins)) if margins else None,
        "independent_feasible_sine_square_and_positive_quadratic_completion_controls":3*len(checked),
        "old_v4_mathematics_honestly_REUSED_NOT_fresh_all_old_leaf_arithmetic_replayed":True,
        "actual_scope_retention_subset_and_target_rejection_controls":rejected,
        "arithmetic_only_NOT_latest_source_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_whole_leaf_energy_controls_completed_NOT_geometry_admission":True,
                      "new_whole_old_OPEN_leaves":len(checked),"remaining_OPEN":len(remaining),
                      "independent_sine_square_controls":3*len(checked),"rejection_controls":len(rejected),
                      "global_optimality_proved":False}),flush=True)


if __name__ == "__main__":
    main()
