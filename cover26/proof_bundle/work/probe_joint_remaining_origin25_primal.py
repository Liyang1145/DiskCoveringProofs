"""Joint anchor/free primal suggestions on the SAME two checked origin domains.

Allows all15 original anchor angles inside exact source boxes; no narrowing,
symmetry, proof cache or source mutation. Exact rod/origin checks decide DATA.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

from audit_prefix_partition import linux
import probe_remaining_origin25_primal_relaxation as previous
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-joint-anchor-actual-two-origin25-primal-relaxation-v1"
FIXED = Path("outputs/n26-actual-two-origin25-OPEN-primal-relaxation-diagnostic-v1.json")
FIXED_SHA = "f6a823d876eea8547bae03afeeca9d65d267daf97e0586c3a5b4ac9416b01793"


def joint_suggestion(original,model,leaf,start,iterations):
    lo,hi = np.array(list(map(float,map(F,leaf["lower"])))),np.array(list(map(float,map(F,leaf["upper"]))))
    widths = hi-lo
    fixed_turns = np.array(list(map(float,map(F,start["actual_fixed_feasible_anchor_turns"]))))
    initial_free = np.array([[float(F(value)) for value in point] for point in start["rational60_free_points"]])
    rows,rhs = [],[]
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            vector = np.zeros(15)
            if i:
                vector[i-1] += widths[i-1]
            if j:
                vector[j-1] -= widths[j-1]
            fixed = (lo[i-1] if i else 0)-(lo[j-1] if j else 0)
            constant = float(F(original["matrix"][i][j],10**40))+fixed
            scale = max(float(max(abs(vector))),abs(constant),1e-10)
            rows.append(vector/scale)
            rhs.append(constant/scale)
    rows,rhs = np.array(rows),np.array(rhs)
    edges = np.array(model["edges"])
    def positions(x):
        turns = np.r_[0.,lo+widths*x[120:135]]
        anchors = np.column_stack((np.cos(2*np.pi*turns),np.sin(2*np.pi*turns)))
        return np.vstack((anchors,x[:120].reshape(60,2))),anchors
    def constraints(x):
        p,_ = positions(x)
        deltas = p[edges[:,0]]-p[edges[:,1]]
        free = p[16:]
        return np.r_[x[-1]-np.einsum("ij,ij->i",deltas,deltas),
                     1-np.einsum("ij,ij->i",free,free),
                     x[-1]-free[25]@free[25],rhs+rows@x[120:135]]
    def jacobian(x):
        p,anchors = positions(x)
        anchor_derivatives = 2*np.pi*np.column_stack((-anchors[1:,1],anchors[1:,0]))*widths[:,None]
        jac = np.zeros((435,136))
        for index,(u,v) in enumerate(model["edges"]):
            delta = p[u]-p[v]
            if u >= 16:
                jac[index,2*(u-16):2*(u-16)+2] -= 2*delta
            elif u:
                jac[index,120+u-1] -= 2*delta@anchor_derivatives[u-1]
            if v >= 16:
                jac[index,2*(v-16):2*(v-16)+2] += 2*delta
            elif v:
                jac[index,120+v-1] += 2*delta@anchor_derivatives[v-1]
            jac[index,-1] = 1
        for i,point in enumerate(p[16:]):
            jac[134+i,2*i:2*i+2] = -2*point
        jac[194,50:52] = -2*p[41]
        jac[194,-1] = 1
        jac[195:,120:135] = rows
        return jac
    scaled = np.array([.5 if width == 0 else np.clip((turn-a)/width,0.,1.)
                       for turn,a,width in zip(fixed_turns,lo,widths)])
    initial = np.r_[initial_free.ravel(),scaled,float(F(start["exact_result"]["exact_outward_necessary_model_radius"])**2)+1e-5]
    h,error = 1e-6,0.
    actual_jacobian = jacobian(initial)
    for column in (0,50,51,119,120,126,130,134,135):
        left,right = initial.copy(),initial.copy()
        left[column] += h
        right[column] -= h
        finite = (constraints(left)-constraints(right))/(2*h)
        error = max(error,float(max(abs(finite-actual_jacobian[:,column]))))
    if error > 1e-6:
        raise ValueError("actual joint anchor-origin numerical Jacobian differs")
    bounds = [(-1.,1.)]*120+[(0.,0. if width == 0 else 1.) for width in widths]+[(0.,2.)]
    optimized = minimize(
        lambda x:float(x[-1]),initial,jac=lambda x:np.r_[np.zeros(135),1.],
        method="SLSQP",bounds=bounds,
        constraints={"type":"ineq","fun":constraints,"jac":jacobian},
        options={"ftol":1e-13,"maxiter":iterations,"disp":False})
    if not np.all(np.isfinite(optimized.x)):
        raise ValueError("joint origin numerical suggestions nonfinite")
    return lo+widths*optimized.x[120:135],optimized.x[:120].reshape(60,2),{
        "numerical_joint_anchor_free_origin_success_NOT_proof":bool(optimized.success),
        "numerical_message":str(optimized.message),"numerical_iterations":int(optimized.nit),
        "numerical_minimum_constraint_NOT_proof":float(min(constraints(optimized.x))),
        "numerical_minimax_squared_radius_NOT_proof":float(optimized.x[-1]),
        "actual_joint_Jacobian_finite_difference_error_NOT_proof":error,
    }


def exact_turns(original,leaf,angles):
    matrix = original["matrix"]
    lo,hi = list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))
    mixed = previous.source.original_source.original_source.mixed
    for epsilon in (F(0),F(1,10**16),F(1,10**14),F(1,10**12)):
        lower = [max(a,min(b,F(round(float(value)*10**16),10**16)-epsilon))
                 for value,a,b in zip(angles,lo,hi)]
        box = mixed.old.prior.prior.tighten(matrix,lower,hi)
        if box is None:
            continue
        try:
            previous.source.energy.scalar.full.hull.quadratic.reference_gate(box[0],lo,hi,matrix)
        except ValueError:
            continue
        return box[0],{"rational_feasible_angle_recovery_epsilon":str(epsilon),
                       "exact_original_closed_box_AND_all_difference_inequalities_checked":True}
    # Numerical projection failure supplies NO infeasibility claim.
    candidate = [(a+b)/2 for a,b in zip(lo,hi)]
    previous.source.energy.scalar.full.hull.quadratic.reference_gate(candidate,lo,hi,matrix)
    return candidate,{"numerical_angles_failed_exact_projection_midpoint_used":True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--iterations",type=int,default=700)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.iterations <= 1500:
        raise ValueError("fresh bounded joint origin primal diagnostic required")
    original,model,bases,seed,pending,arcs,inventory = previous.inputs()
    if binding.sha(FIXED) != FIXED_SHA:
        raise ValueError("joint primal initialization changed exact fixed-anchor diagnostic")
    fixed = binding.read(FIXED)
    by_index = {item["actual_retained_origin25_OPEN_subleaf"]["index"]:item for item in fixed["results"]}
    radius_lower = binding.read(previous.source.original_source.original_source.CURRENT)["r_strict_interval"][0]
    results = []
    for leaf in pending:
        angles,free,numerical = joint_suggestion(original,model,leaf,by_index[leaf["index"]],args.iterations)
        turns,angle_controls = exact_turns(original,leaf,angles)
        rational = [[str(F(round(float(value)*10**17),10**17)) for value in point] for point in free]
        exact = previous.exact_result(original,model,leaf,turns,rational,radius_lower,arcs)
        results.append({
            "actual_retained_origin25_OPEN_subleaf":leaf,"actual_fixed_feasible_anchor_turns":list(map(str,turns)),
            "rational60_free_points":rational,"exact_result":exact,
            "numerical_joint_suggestions_NOT_proofs":numerical,"exact_angle_recovery":angle_controls,
        })
        print(json.dumps({
            "actual_retained_origin25_subleaf":leaf["index"],
            "joint_exact_below_Rstar_necessary_model_AND_origin25":exact[
                "exact_below_Rstar_134rod_AND_origin25_NECESSARY_model_realization"],
            "exact_radius_margin_display":float(F(exact["exact_radius_margin_below_Rstar_LOWER"])),
            "continuous_cover_proved":False,"formal_payments":0,
        }),flush=True)
    inventory.update({
        linux(FIXED):FIXED_SHA,linux(__file__):binding.sha(__file__),
        linux(previous.__file__):binding.sha(previous.__file__),
    })
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("joint origin actual input changed")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_whole_prior_leaf_index":2641,
        "actual_partial_branch_diagnosis_sha256":previous.SEED_SHA,
        "actual_partial_branch_controls_sha256":previous.CONTROL_SHA,
        "fixed_anchor_initialization_diagnosis_sha256":FIXED_SHA,
        "all15_original_anchor_angles_and60free_points_varied_NO_symmetry":True,"results":results,
        "all_original919_and6partial_strict_proofs_UNMODIFIED":True,
        "independent_exact_joint_primal_witness_controls_STILL_required":True,
        "these_are_necessary_model_realizations_NOT_continuous_covers":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")


if __name__ == "__main__":
    main()
