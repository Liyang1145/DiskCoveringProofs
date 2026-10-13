"""Independent exact rod/angle/origin checks for actual retained primal DATA."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_remaining_origin25_primal_relaxation as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-retained-origin25-primal-relaxation-controls-v1"


def independent_witness(original,model,leaf,item,radius_lower,arcs,require_below=False):
    turns = [F(0),*map(F,item["actual_fixed_feasible_anchor_turns"])]
    free = [list(map(F,point)) for point in item["rational60_free_points"]]
    if len(turns) != 16 or len(free) != 60 or any(len(point) != 2 for point in free):
        raise ValueError("independent primal witness changed actual dimensions")
    for value,a,b in zip(turns[1:],leaf["lower"],leaf["upper"]):
        if not F(a) <= value <= F(b):
            raise ValueError("independent primal angle is outside actual retained closed subleaf")
    for i in range(16):
        for j in range(16):
            if turns[j]-turns[i] > F(original["matrix"][i][j],10**40):
                raise ValueError("independent primal angle violates original necessary difference")
    cosines,sines = [],[]
    for value in turns:
        cosine,sine = arcs.sincos_turn(value)
        cosines.append(tuple(F(x,arcs.SCALE) for x in cosine))
        sines.append(tuple(F(x,arcs.SCALE) for x in sine))
    squared = []
    for u,v in model["edges"]:
        if u >= 16 and v >= 16:
            squared.append(sum((a-b)**2 for a,b in zip(free[u-16],free[v-16])))
        elif u < 16 <= v:
            x,y = free[v-16]
            squared.append(max((cosines[u][0]-x)**2,(cosines[u][1]-x)**2)
                           +max((sines[u][0]-y)**2,(sines[u][1]-y)**2))
        elif v < 16 <= u:
            x,y = free[u-16]
            squared.append(max((cosines[v][0]-x)**2,(cosines[v][1]-x)**2)
                           +max((sines[v][0]-y)**2,(sines[v][1]-y)**2))
        else:
            raise ValueError("actual134-rod source unexpectedly has anchor-to-anchor rods")
    norm = sum(value*value for value in free[25])
    radius = F(item["exact_result"]["exact_outward_necessary_model_radius"])
    rod_margin = min(radius*radius-value for value in squared)
    origin_margin = radius*radius-norm
    disk_margin = min(1-sum(value*value for value in point) for point in free)
    below = rod_margin > 0 and origin_margin > 0 and disk_margin >= 0 and radius < F(radius_lower)
    claimed = item["exact_result"]
    if (
        list(map(str,squared)) != claimed["exact_all134_rod_squared_distance_upper_bounds"]
        or str(norm) != claimed["exact_origin_center_squared_norm"]
        or str(rod_margin) != claimed["exact_minimum_all134_rod_squared_distance_margin"]
        or str(origin_margin) != claimed["exact_origin_cover_squared_margin"]
        or str(disk_margin) != claimed["exact_minimum_free_unit_disk_margin"]
        or F(radius_lower)-radius != F(claimed["exact_radius_margin_below_Rstar_LOWER"])
        or (disk_margin >= 0) != claimed["all60_free_centers_and_witnesses_inside_unit_disk"]
        or below != claimed["exact_below_Rstar_134rod_AND_origin25_NECESSARY_model_realization"]
        or claimed["actual_origin_covering_original_center_label"] != 25
        or claimed["continuous_unit_disk_cover_NOT_proved"] is not True
        or claimed["actual_empty_circumcircles_embedding_and_full_area_partition_NOT_enforced"] is not True
        or claimed["NOT_a_counterexample_to_n26_global_optimality"] is not True
    ):
        raise ValueError("independent exact primal distance/origin/radius/scope witness differs")
    if require_below and not below:
        raise ValueError("this necessary-model witness is NOT strictly below the exact candidate lower radius")
    return {
        "actual_retained_origin25_subleaf_index":leaf["index"],
        "all134_actual_rods_independently_bounded":134,
        "all240_nontrivial_necessary_angle_differences_checked":True,
        "exact_necessary_model_radius":str(radius),
        "exact_radius_margin_below_Rstar_LOWER":str(F(radius_lower)-radius),
        "exact_rod_squared_margin":str(rod_margin),"exact_origin_squared_margin":str(origin_margin),
        "all60_original_free_points_in_unit_disk":disk_margin >= 0,
        "below_Rstar_rods_AND_origin25_relaxation_feasible":below,
        "actual_continuous_disk_cover_NOT_proved":True,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh independent output and actual completed primal diagnosis required")
    diagnosis = binding.read(args.diagnosis)
    if (
        diagnosis["schema"] != producer.SCHEMA
        or diagnosis["actual_partial_branch_diagnosis_sha256"] != producer.SEED_SHA
        or diagnosis["actual_partial_branch_controls_sha256"] != producer.CONTROL_SHA
        or diagnosis["executed_producer_sha256"] != binding.sha(producer.__file__)
        or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
        or diagnosis["global_optimality_proved"] is not False
    ):
        raise ValueError("independent primal diagnostic changed source/arithmetic-only scope")
    for text,digest in diagnosis["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("completed primal prerequisite changed")
    original,model,bases,seed,pending,arcs,inventory = producer.inputs()
    radius_lower = binding.read(producer.source.original_source.original_source.CURRENT)["r_strict_interval"][0]
    by_index = {leaf["index"]:leaf for leaf in pending}
    checked,seen = [],set()
    for item in diagnosis["results"]:
        leaf = item["actual_retained_origin25_OPEN_subleaf"]
        if leaf["index"] in seen or by_index.get(leaf["index"]) != leaf:
            raise ValueError("independent primal witness changed exact actual retained domain")
        seen.add(leaf["index"])
        result = independent_witness(original,model,leaf,item,radius_lower,arcs)
        checked.append(result)
        print(json.dumps({"independent_exact_origin25_primal_subleaf":leaf["index"],
                          "below_root_necessary_model":result["below_Rstar_rods_AND_origin25_relaxation_feasible"],
                          "not_a_disk_cover_proof":True}),flush=True)
    if seen != set(by_index):
        raise ValueError("independent primal diagnosis omitted an actual retained subleaf")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid exact origin primal control accepted: "+label)
    exemplar = diagnosis["results"][0]
    leaf = exemplar["actual_retained_origin25_OPEN_subleaf"]
    changed = deepcopy(exemplar)
    changed["actual_fixed_feasible_anchor_turns"][0] = "0"
    reject("actual-closed-angle-domain-violated",lambda:independent_witness(original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(exemplar)
    changed["rational60_free_points"].pop()
    reject("free-witness-omitted",lambda:independent_witness(original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(exemplar)
    changed["rational60_free_points"][25] = ["2","0"]
    reject("actual-origin-covering-center-forged",lambda:independent_witness(original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(exemplar)
    changed["exact_result"]["exact_outward_necessary_model_radius"] = "1/1000"
    reject("unpaid-rods-by-forged-tiny-radius",lambda:independent_witness(original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(exemplar)
    changed["exact_result"]["exact_all134_rod_squared_distance_upper_bounds"].pop()
    reject("one-original-rod-distance-omitted",lambda:independent_witness(original,model,leaf,changed,radius_lower,arcs))
    changed = deepcopy(exemplar)
    changed["exact_result"]["continuous_unit_disk_cover_NOT_proved"] = False
    reject("necessary-model-promoted-to-continuous-cover",lambda:independent_witness(original,model,leaf,changed,radius_lower,arcs))
    for text,digest in diagnosis["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("actual primal inputs changed during independent distance checks")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual primal diagnosis changed during independent checks")
    inventory.update(diagnosis["input_sha256"])
    inventory.update({linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__)})
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_whole_prior_leaf_index":2641,
        "diagnosis_sha256":args.diagnosis_sha256,
        "actual_partial_branch_diagnosis_sha256":producer.SEED_SHA,
        "actual_partial_branch_controls_sha256":producer.CONTROL_SHA,
        "actual_exact_primal_witnesses_independently_checked":checked,
        "actual_retained_origin25_below_root_necessary_model_realizations":sum(
            result["below_Rstar_rods_AND_origin25_relaxation_feasible"] for result in checked),
        "these_witnesses_DO_NOT_prove_continuous_unit_disk_cover_or_optimality_counterexample":True,
        "all_actual_original919_and6partial_strict_payments_UNMODIFIED":True,
        "actual_distance_angle_origin_radius_and_scope_rejection_controls":rejected,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"independent_exact_retained_origin25_primal_controls_completed":True,
                      "actual_below_root_necessary_model_realizations":report[
                          "actual_retained_origin25_below_root_necessary_model_realizations"],
                      "actual_rejection_controls":len(rejected),"new_geometric_payments":0}),flush=True)


if __name__ == "__main__":
    main()
