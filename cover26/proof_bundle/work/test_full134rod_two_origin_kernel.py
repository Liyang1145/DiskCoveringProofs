"""Actual two-owner/augmented-kernel arithmetic controls, not leaf admission."""

from copy import deepcopy
from fractions import Fraction as F
import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_full134rod_two_origin_kernel as origin
import probe_root25_v4_balanced_whole_leaf_energy as source
import verify_conditional_force_stage as binding


def independent_identity(base,kernel):
    den,scale = base["inverse_denominator"],base["scale"]
    mu,owner = kernel["origin_multiplier"],kernel["origin_center_label"]
    R = F(scale*base["inverse"][owner][owner],den)
    k = mu/(1+mu*R)
    h = [F(value,den) for value in base["harmonic"][owner]]
    column = [F(scale*base["inverse"][i][owner],den) for i in range(60)]
    extension = [
        [F(value,den)-k*column[i]*h[j] for j,value in enumerate(row)]
        for i,row in enumerate(base["harmonic"])
    ]
    if (
        k != kernel["boundary_origin_constant"]
        or kernel["radius_squared_budget_weight"] != F(sum(base["weights"]),scale)+mu
        or any(min(row) < 0 or not 0 <= sum(row) <= 1 for row in extension)
    ):
        raise ValueError("independent origin constant/budget/substochastic extension changed")
    # Nonunit anchors make the essential nonzero row-sum term visible.
    anchors = [[F((3*i+1)%7-3,5),F((5*i+2)%11-5,7)] for i in range(16)]
    free = [[F((7*i+3)%13-6,11),F((11*i+4)%17-8,13)] for i in range(60)]
    points = anchors+free
    direct = sum(F(weight,scale)*sum((points[u][d]-points[v][d])**2 for d in range(2))
                 for (u,v),weight in zip(base["edges"],base["weights"]))
    direct += mu*sum(value*value for value in free[owner])
    boundary = sum(
        F(weight,kernel["energy_denominator"])*sum((anchors[i][d]-anchors[j][d])**2 for d in range(2))
        for i,j,weight in kernel["pairs"])
    rowsum = k*sum(value*sum(x*x for x in anchor) for value,anchor in zip(h,anchors))
    boundary += rowsum
    deviations = [
        [free[i][d]-sum(weight*anchors[j][d] for j,weight in enumerate(extension[i])) for d in range(2)]
        for i in range(60)
    ]
    zeros = [[F(0),F(0)] for _ in range(16)]+deviations
    residual = sum(
        F(weight,scale)*sum((zeros[u][d]-zeros[v][d])**2 for d in range(2))
        for (u,v),weight in zip(base["edges"],base["weights"]))
    residual += mu*sum(value*value for value in deviations[owner])
    if direct != boundary+residual or min(boundary,residual) < 0:
        raise ValueError("independent actual origin-ground square completion failed")
    return {
        "arbitrary_nonunit_anchors_and_nonharmonic60_free_points_square_completion":True,
        "nonzero_Schur_row_sum_energy_term_explicitly_retained":str(rowsum),
        "radius_budget_includes_virtual_mu_NOT135physical_rods":True,
        "independent_positive_origin_constant":str(k),
        "independent_residual_energy":str(residual),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("new distinct two-origin arithmetic controls required")
    original,model,kernels,seed,seed_controls,row,pending,arcs,inventory = source.source_inputs()
    path = original["data"][3]
    eligible = origin.eligible_centers(path)
    base = kernels[1]
    W = F(sum(base["weights"]),base["scale"])
    controls = []
    for owner in eligible:
        for ratio in (F(0),F(1,10),F(1),F(10)):
            kernel = origin.kernel_gate(base,path,owner,ratio*W)
            identity = independent_identity(base,kernel)
            controls.append({
                "origin_center_label":owner,"mu_over_original_physical_rod_weight_sum":str(ratio),
                "all3600_augmented_ground_inverse_products_exactly_checked":True,
                "independent_identity":identity,
            })
            print(json.dumps({"actual_origin_center":owner,"mu_over_W":str(ratio),
                              "exact_augmented_inverse_and_independent_square_completion":True}),flush=True)
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid distinct origin kernel accepted: "+label)
    reject("ineligible-boundary-adjacent-center",lambda:origin.kernel_gate(base,path,17,W))
    reject("negative-origin-conductance",lambda:origin.kernel_gate(base,path,16,-W))
    bad_path = deepcopy(path)
    bad_path["states"][-1]["adjacency"][0] |= 1<<24
    reject("source-exposure-changed-without-face-map",lambda:origin.kernel_gate(base,bad_path,16,W))
    bad_path = deepcopy(path)
    bad_path["native_to_exact_candidate_labels"]["24"] = 17
    reject("nonbijective-origin-owner-map",lambda:origin.kernel_gate(base,bad_path,16,W))
    bad = {**base,"distinct_full134rod_60free_positive_candidate_kernel":False}
    reject("old92rod-or-unverified-base-kernel-relabelled",lambda:origin.kernel_gate(bad,path,16,W))
    bad = deepcopy(base)
    bad["inverse"][0][0] += 1
    reject("changed-original-inverse-in-rank-one-formula",lambda:origin.kernel_gate(bad,path,16,W))
    kernel = origin.kernel_gate(base,path,16,W)
    bad = {**kernel,"boundary_origin_constant":F(0)}
    reject("essential-origin-Schur-constant-omitted",lambda:independent_identity(base,bad))
    bad = {**kernel,"radius_squared_budget_weight":W}
    reject("virtual-origin-weight-omitted-from-radius-budget",lambda:independent_identity(base,bad))
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("actual original source changed during two-origin controls")
    inventory.update({
        linux(origin.__file__):binding.sha(origin.__file__),linux(__file__):binding.sha(__file__),
        linux("work/n26-full134rod-two-origin-branches-proof.md"):binding.sha(
            "work/n26-full134rod-two-origin-branches-proof.md"),
    })
    report = {
        "schema":"N26-independent-actual-two-origin-owner-full134rod-kernel-controls-v1",
        "verified":False,"new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "actual_complete_candidate_native_origin_eligible_labels":[24,25],
        "actual_complete_candidate_exact_origin_eligible_labels":eligible,
        "full_vertex_face_and_independent_exposure_source_reconstructed":True,
        "actual_augmented_kernel_identity_controls":controls,
        "all_old134_physical_rods_unchanged_origin_multiplier_separately_labelled":True,
        "both_origin_branches_required_for_any_future_whole_leaf_exclusion":True,
        "actual_inverse_source_constant_and_budget_rejection_controls":rejected,
        "whole_leaf_origin_branch_lower_bounds_NOT_yet_implemented_or_admitted":True,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "actual_two_origin_branch_kernel_arithmetic_controls_completed_NOT_admission":True,
        "eligible_original_centers":eligible,"exact_kernel_controls":len(controls),
        "actual_rejection_controls":len(rejected),"new_geometric_payments":0,
    }),flush=True)


if __name__ == "__main__":
    main()
