"""Independent exact joint-angle rod/origin witnesses on both retained boxes."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_joint_remaining_origin25_primal as producer
import test_remaining_origin25_primal_relaxation as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-joint-anchor-actual-two-origin25-primal-controls-v1"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("new exact completed joint primal diagnostic required")
    diagnosis = binding.read(args.diagnosis)
    if (
        diagnosis["schema"] != producer.SCHEMA
        or diagnosis["actual_partial_branch_diagnosis_sha256"] != producer.previous.SEED_SHA
        or diagnosis["actual_partial_branch_controls_sha256"] != producer.previous.CONTROL_SHA
        or diagnosis["executed_producer_sha256"] != binding.sha(producer.__file__)
        or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
        or diagnosis["global_optimality_proved"] is not False
        or diagnosis["these_are_necessary_model_realizations_NOT_continuous_covers"] is not True
    ):
        raise ValueError("joint primal report changed actual retained source/qualified scope")
    for text,digest in diagnosis["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("joint primal selected input changed")
    original,model,bases,seed,pending,arcs,inventory = producer.previous.inputs()
    radius_lower = binding.read(producer.previous.source.original_source.original_source.CURRENT)["r_strict_interval"][0]
    by_index,seen = {leaf["index"]:leaf for leaf in pending},set()
    checked = []
    for item in diagnosis["results"]:
        leaf = item["actual_retained_origin25_OPEN_subleaf"]
        if leaf["index"] in seen or by_index.get(leaf["index"]) != leaf:
            raise ValueError("joint primal witness omitted/changed a whole retained domain")
        seen.add(leaf["index"])
        result = independent.independent_witness(original,model,leaf,item,radius_lower,arcs)
        checked.append(result)
        print(json.dumps({"independent_joint_angle_origin25_primal_subleaf":leaf["index"],
                          "exact_below_candidate_necessary_model":result[
                              "below_Rstar_rods_AND_origin25_relaxation_feasible"],
                          "NOT_a_continuous_disk_cover":True}),flush=True)
    if seen != set(by_index):
        raise ValueError("joint exact witness report lost one retained domain")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid joint primal witness accepted: "+label)
    item = diagnosis["results"][0]
    leaf = item["actual_retained_origin25_OPEN_subleaf"]
    changed = deepcopy(item)
    changed["actual_fixed_feasible_anchor_turns"][0] = "0"
    reject("outside-actual-retained-angle-domain",lambda:independent.independent_witness(
        original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(item)
    changed["rational60_free_points"][25] = ["2","0"]
    reject("actual-origin25-center-outside-radius",lambda:independent.independent_witness(
        original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(item)
    changed["exact_result"]["exact_outward_necessary_model_radius"] = "1/1000"
    reject("all-original-rods-undercharged-by-tiny-radius",lambda:independent.independent_witness(
        original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(item)
    changed["exact_result"]["continuous_unit_disk_cover_NOT_proved"] = False
    reject("necessary-model-promoted-to-disk-cover",lambda:independent.independent_witness(
        original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(item)
    changed["exact_result"]["exact_all134_rod_squared_distance_upper_bounds"].pop()
    reject("original-rod-omitted",lambda:independent.independent_witness(
        original,model,leaf,changed,radius_lower,arcs))
    for text,digest in diagnosis["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("joint primal witness actual source changed during independent check")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("joint primal diagnostic changed during independent check")
    inventory.update(diagnosis["input_sha256"])
    inventory.update({
        linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__),
        linux(independent.__file__):binding.sha(independent.__file__),
    })
    positive = sum(item["below_Rstar_rods_AND_origin25_relaxation_feasible"] for item in checked)
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_whole_prior_leaf_index":2641,
        "diagnosis_sha256":args.diagnosis_sha256,
        "actual_partial_branch_diagnosis_sha256":producer.previous.SEED_SHA,
        "actual_partial_branch_controls_sha256":producer.previous.CONTROL_SHA,
        "all_actual_joint_angle_origin25_exact_witnesses_independently_checked":checked,
        "actual_below_root_134rod_AND_origin25_necessary_model_realizations":positive,
        "these_are_NOT_disk_covers_or_n26_optimality_counterexamples":True,
        "a_sound_rods_AND_origin_ONLY_argument_cannot_exclude_positive_witness_domains":positive > 0,
        "failure_to_find_a_witness_does_NOT_prove_infeasibility":True,
        "all_original919_and6partial_strict_payments_UNMODIFIED":True,
        "actual_angle_distance_origin_budget_and_scope_rejection_controls":rejected,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_exact_joint_origin25_primal_controls_completed":True,
                      "positive_below_root_necessary_model_witnesses":positive,
                      "actual_rejection_controls":len(rejected),"formal_geometric_payments":0}),flush=True)


if __name__ == "__main__":
    main()
