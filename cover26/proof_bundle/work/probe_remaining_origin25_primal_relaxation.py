"""Exact fixed-anchor primal diagnosis of the two retained origin25 regions.

Below-root NECESSARY-model realizations, if found, are NOT disk covers.
No forest/receipt/source mutation; numerics propose points, exact bounds decide.
"""

import argparse
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

from audit_prefix_partition import linux
import probe_latest_origin_branch_closed_forest as source
import verify_conditional_force_stage as binding


SEED = Path("outputs/n26-latest919-origin25-leaf2641-closed-forest-diagnostic-v1.json")
CONTROLS = Path("outputs/n26-latest919-origin25-leaf2641-closed-forest-independent-controls-v1.json")
SEED_SHA = "9a6f48cb160c1aecd15755fc4678919f21c1e207f93e6a1a2bf40a4f0a54b331"
CONTROL_SHA = "6967e48554cba7447b95529d4671ccee410d907e1e867c828171d2d5fc4ddf20"
SCHEMA = "N26-unaccepted-actual-two-retained-origin25-primal-relaxation-diagnosis-v1"


def inputs():
    original,model,bases,prior,prior_controls,whole_leaf,whole16,arcs,inventory = source.inputs()
    if binding.sha(SEED) != SEED_SHA or binding.sha(CONTROLS) != CONTROL_SHA:
        raise ValueError("primal diagnostic requires actual checked6-strict/2-OPEN branch history")
    seed,controls = binding.read(SEED),binding.read(CONTROLS)
    if (
        controls["diagnosis_sha256"] != SEED_SHA or seed["actual_latest919_OPEN_leaf"] != whole_leaf
        or seed["whole_origin16_branch_prior_checked_proof"] != whole16
        or seed["entire_origin25_closed_branch_strictly_excluded"] is not False
        or controls["entire_origin25_closed_branch_strictly_excluded"] is not False
        or len(seed["retained_origin25_closed_OPEN_subleaves"]) != 2
        or seed["retained_origin25_closed_OPEN_subleaves"] != controls["retained_origin25_closed_OPEN_subleaves"]
        or any(record["verified"] is not False or record["new_geometric_payments"] != 0
               or record["global_optimality_proved"] is not False for record in (seed,controls))
    ):
        raise ValueError("primal diagnostic reset/changed actual retained origin25 source")
    for record in (seed,controls):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("primal diagnostic completed branch prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("primal original-model prerequisite digest conflict")
            inventory[text] = digest
    mixed = source.original_source.original_source.mixed
    primary = source.domains(original["matrix"],whole_leaf,seed["origin25_closed_forest_nodes"],
                             mixed.old.prior.prior.tighten,False)
    independent = source.domains(original["matrix"],whole_leaf,seed["origin25_closed_forest_nodes"],
                                 mixed.old.prior.prior.independently_contract,True)
    pending = [leaf for leaf in primary if leaf["kind"] == "OPEN"]
    if primary != independent or pending != seed["retained_origin25_closed_OPEN_subleaves"]:
        raise ValueError("primal diagnostic changed actual two retained closed domains")
    inventory.update({
        linux(SEED):SEED_SHA,linux(CONTROLS):CONTROL_SHA,linux(__file__):binding.sha(__file__),
        linux("work/n26-origin25-primal-relaxation-scope-proof.md"):binding.sha(
            "work/n26-origin25-primal-relaxation-scope-proof.md"),
    })
    return original,model,bases,seed,pending,arcs,inventory


def numerical_minimax(model,base,turns,owner,iterations):
    anchors = np.array([[np.cos(2*np.pi*float(turn)),np.sin(2*np.pi*float(turn))]
                        for turn in [F(0),*turns]])
    den = base["inverse_denominator"]
    harmonic = np.array([[float(F(value,den)) for value in row] for row in base["harmonic"]])
    initial_free = harmonic@anchors
    # Starting near the origin branch is a suggestion only.
    initial_free[owner] *= .2
    edges = np.array(model["edges"])
    left,right = edges[:,0],edges[:,1]
    def points(x):
        return np.vstack((anchors,x[:120].reshape(60,2)))
    def constraints(x):
        p = points(x)
        free = p[16:]
        differences = p[left]-p[right]
        rods = np.einsum("ij,ij->i",differences,differences)
        return np.r_[x[-1]-rods,1-np.einsum("ij,ij->i",free,free),
                     x[-1]-np.dot(free[owner],free[owner])]
    def jacobian(x):
        p = points(x)
        jac = np.zeros((195,121))
        for index,(u,v) in enumerate(model["edges"]):
            difference = p[u]-p[v]
            if u >= 16:
                jac[index,2*(u-16):2*(u-16)+2] -= 2*difference
            if v >= 16:
                jac[index,2*(v-16):2*(v-16)+2] += 2*difference
            jac[index,-1] = 1
        for index,point in enumerate(p[16:]):
            jac[134+index,2*index:2*index+2] = -2*point
        jac[194,2*owner:2*owner+2] = -2*p[16+owner]
        jac[194,-1] = 1
        return jac
    initial = np.r_[initial_free.ravel(),1.]
    values = constraints(initial)
    initial[-1] = 1-min(0,float(min(values)))+1e-4
    h,error = 1e-6,0.
    exact_jacobian = jacobian(initial)
    for column in (0,17,50,51,119,120):
        a,b = initial.copy(),initial.copy()
        a[column] += h
        b[column] -= h
        numerical = (constraints(a)-constraints(b))/(2*h)
        error = max(error,float(max(abs(numerical-exact_jacobian[:,column]))))
    if error > 1e-6:
        raise ValueError("actual origin minimax numerical Jacobian control failed")
    result = minimize(lambda x:float(x[-1]),initial,jac=lambda x:np.r_[np.zeros(120),1.],
                      method="SLSQP",bounds=[(-1.,1.)]*120+[(0.,2.)],
                      constraints={"type":"ineq","fun":constraints,"jac":jacobian},
                      options={"ftol":1e-13,"maxiter":iterations,"disp":False})
    if not np.all(np.isfinite(result.x)):
        raise ValueError("actual origin minimax suggestion was nonfinite")
    free = result.x[:120].reshape(60,2)
    return free,{
        "numerical_minimax_success_NOT_proof":bool(result.success),
        "numerical_minimax_message":str(result.message),"numerical_iterations":int(result.nit),
        "numerical_radius_squared_NOT_certificate":float(result.x[-1]),
        "numerical_constraint_minimum_NOT_proof":float(min(constraints(result.x))),
        "actual_Jacobian_finite_difference_error_NOT_proof":error,
    }


def exact_result(original,model,leaf,turns,free_points,radius_lower,arcs):
    if (
        len(turns) != 15 or len(free_points) != 60
        or any(len(point) != 2 for point in free_points)
        or len(model["edges"]) != 134 or model["vertices"] != 76
    ):
        raise ValueError("origin primal exact witness changed134rod/60free/15angle dimension")
    source.energy.scalar.full.hull.quadratic.reference_gate(turns,leaf["lower"],leaf["upper"],original["matrix"])
    positions = []
    for turn in [F(0),*map(F,turns)]:
        cosine,sine = arcs.sincos_turn(turn)
        positions.append([(F(a,arcs.SCALE),F(b,arcs.SCALE)) for a,b in (cosine,sine)])
    free = [list(map(F,point)) for point in free_points]
    positions.extend([[(coordinate,coordinate) for coordinate in point] for point in free])
    distances = []
    for u,v in model["edges"]:
        distances.append(sum(max((a-d)**2,(b-c)**2)
                             for (a,b),(c,d) in zip(positions[u],positions[v])))
    origin_norm2 = sum(value*value for value in free[25])
    maximum,grid = max([*distances,origin_norm2]),10**15
    numerator = isqrt(maximum.numerator*grid*grid//maximum.denominator)
    if F(numerator,grid)**2 < maximum:
        numerator += 1
    radius = F(numerator+1,grid)
    rod_margin = min(radius*radius-value for value in distances)
    origin_margin = radius*radius-origin_norm2
    disk_margin = min(1-sum(value*value for value in point) for point in free)
    if rod_margin <= 0 or origin_margin <= 0:
        raise AssertionError("exact outward origin primal radius failed to cover all necessary constraints")
    below = radius < F(radius_lower) and disk_margin >= 0
    return {
        "exact_all134_rod_squared_distance_upper_bounds":list(map(str,distances)),
        "actual_origin_covering_original_center_label":25,
        "exact_origin_center_squared_norm":str(origin_norm2),
        "exact_outward_necessary_model_radius":str(radius),
        "exact_minimum_all134_rod_squared_distance_margin":str(rod_margin),
        "exact_origin_cover_squared_margin":str(origin_margin),
        "all60_free_centers_and_witnesses_inside_unit_disk":disk_margin >= 0,
        "exact_minimum_free_unit_disk_margin":str(disk_margin),
        "exact_radius_margin_below_Rstar_LOWER":str(F(radius_lower)-radius),
        "exact_below_Rstar_134rod_AND_origin25_NECESSARY_model_realization":below,
        "continuous_unit_disk_cover_NOT_proved":True,
        "actual_empty_circumcircles_embedding_and_full_area_partition_NOT_enforced":True,
        "NOT_a_counterexample_to_n26_global_optimality":True,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--iterations",type=int,default=500)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.iterations <= 1000:
        raise ValueError("new bounded exact primal diagnostic required")
    original,model,bases,seed,pending,arcs,inventory = inputs()
    radius_lower = binding.read(source.original_source.original_source.CURRENT)["r_strict_interval"][0]
    results = []
    for leaf in pending:
        turns = [(F(a)+F(b))/2 for a,b in zip(leaf["lower"],leaf["upper"])]
        free,numerical = numerical_minimax(model,bases[1],turns,25,args.iterations)
        rational = [[str(F(round(float(value)*10**17),10**17)) for value in point] for point in free]
        exact = exact_result(original,model,leaf,turns,rational,radius_lower,arcs)
        results.append({"actual_retained_origin25_OPEN_subleaf":leaf,
                        "actual_fixed_feasible_anchor_turns":list(map(str,turns)),
                        "rational60_free_points":rational,"exact_result":exact,
                        "numerical_suggestion_NOT_proof":numerical})
        print(json.dumps({
            "actual_retained_origin25_subleaf":leaf["index"],
            "exact_below_Rstar_necessary_model_AND_origin25":exact[
                "exact_below_Rstar_134rod_AND_origin25_NECESSARY_model_realization"],
            "exact_radius_margin_display":float(F(exact["exact_radius_margin_below_Rstar_LOWER"])),
            "continuous_cover_proved":False,"formal_payments":0,
        }),flush=True)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("actual origin source changed during primal suggestions")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_whole_prior_leaf_index":2641,
        "actual_partial_branch_diagnosis_sha256":SEED_SHA,
        "actual_partial_branch_controls_sha256":CONTROL_SHA,
        "actual_origin25_retained_subleaf_indices":[leaf["index"] for leaf in pending],
        "fresh_actual_original_model_and_both_retained_domains_reconstructed":True,
        "results":results,
        "all_old919_global_and6partial_strict_payments_UNMODIFIED":True,
        "below_root_rod_and_origin_realizations_are_NOT_disk_covers":True,
        "independent_exact_primal_witness_controls_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")


if __name__ == "__main__":
    main()
