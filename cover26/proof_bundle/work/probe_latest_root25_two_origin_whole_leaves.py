"""NEW complete two-origin-branch energy on actual checked920 OPEN leaves."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_latest_root25_origin_source as source
import n26_origin_branch_correlated_energy as energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest-root25-complete-two-origin-branch-whole-leaf-successor-v1"
KIND = "FULL134-TWO-ORIGIN-BRANCHES-ENERGY"
RATIOS = tuple(F(value) for value in ("1/100000","1/10000","1/1000","1/100","1/10","1","10"))


def rank(original,kernels,pending):
    row = binding.read(source.SEED)["actual_source_closed_box"]
    broad = [i for i,(a,b) in enumerate(zip(row["sharp_lower"],row["sharp_upper"]))
             if F(b)-F(a) > F(1,10**7)]
    if len(broad) > 10:
        raise ValueError("two-origin corner ranking refuses unbounded numerical allocation")
    masks = np.arange(1<<len(broad))
    bits = np.array([((masks>>j)&1) for j in range(len(broad))]).T
    prepared = []
    for base in kernels:
        den,scale = base["inverse_denominator"],base["scale"]
        prepared.append({
            "left":np.array([i for i,j,w in base["pairs"]]),
            "right":np.array([j for i,j,w in base["pairs"]]),
            "weights":np.array([float(F(w,base["energy_denominator"])) for i,j,w in base["pairs"]]),
            "W":float(F(sum(base["weights"]),scale)),
            "rows":{owner:np.array([float(F(value,den)) for value in base["harmonic"][owner]])
                    for owner in (16,25)},
            "R":{owner:float(F(scale*base["inverse"][owner][owner],den)) for owner in (16,25)},
        })
    rankings = []
    for number,leaf in enumerate(pending,1):
        lo,hi = np.array(list(map(float,map(F,leaf["lower"])))),np.array(list(map(float,map(F,leaf["upper"]))))
        points = np.tile((lo+hi)/2,(len(masks),1))
        points[:,broad] = lo[broad]+bits*(hi-lo)[broad]
        points = np.column_stack((np.zeros(len(points)+1),np.vstack((points,(lo+hi)/2))))
        anchors = np.exp(2j*np.pi*points)
        branches = {16:[],25:[]}
        for index,item in enumerate(prepared):
            E = 2*(1-np.cos(2*np.pi*(points[:,item["right"]]-points[:,item["left"]])))@item["weights"]
            for owner in (16,25):
                norm2 = np.abs(anchors@item["rows"][owner])**2
                for ratio in RATIOS:
                    mu = float(ratio)*item["W"]
                    k = mu/(1+mu*item["R"][owner])
                    score = float(min((E+k*norm2)/(item["W"]+mu)))-float(original["radius"]**2)
                    branches[owner].append({
                        "origin_center_label":owner,"full_support_index":index,
                        "mu_over_physical_rod_weight_sum":str(ratio),
                        "sampled_corner_score_NOT_lower_bound":score,
                    })
        for owner in branches:
            branches[owner].sort(key=lambda item:item["sampled_corner_score_NOT_lower_bound"],reverse=True)
        rankings.append({
            "actual_prior_OPEN_leaf_index":leaf["index"],
            "both_branches_sampled_score_NOT_a_lower_bound":min(
                branches[owner][0]["sampled_corner_score_NOT_lower_bound"] for owner in branches),
            "branch_parameter_suggestions":branches,
        })
        if number%200 == 0:
            print(json.dumps({"two_origin_numerical_ranking_ONLY":number,"of":len(pending)}),flush=True)
    return sorted(rankings,key=lambda item:item["both_branches_sampled_score_NOT_a_lower_bound"],reverse=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=16)
    parser.add_argument("--parts",type=int,default=8)
    parser.add_argument("--branch-tries",type=int,default=2)
    args = parser.parse_args()
    if (
        args.report.exists() or not 1 <= args.limit <= 128
        or not 1 <= args.parts <= 64 or not 1 <= args.branch_tries <= 4
    ):
        raise ValueError("new two-origin experiment needs fresh bounded output")
    original,model,kernels,seed,seed_controls,row,pending,arcs,inventory = source.source()
    path = original["data"][3]
    eligible = energy.origin.eligible_centers(path)
    kernel_controls_path = Path("outputs/n26-actual-full134rod-two-origin-kernel-independent-controls-v1.json")
    kernel_controls_sha = "2c08b59fa1c0ebf60a7d19eecb317c8b6a08ba3564aab1fdae8455f5ef8459a5"
    if binding.sha(kernel_controls_path) != kernel_controls_sha:
        raise ValueError("two-origin experiment changed its completed augmented-kernel controls")
    inventory.update({
        linux(kernel_controls_path):kernel_controls_sha,
        linux(energy.__file__):binding.sha(energy.__file__),
        linux(energy.origin.__file__):binding.sha(energy.origin.__file__),
        linux(__file__):binding.sha(__file__),
        linux("work/n26-origin-branch-whole-domain-energy-proof.md"):binding.sha(
            "work/n26-origin-branch-whole-domain-energy-proof.md"),
    })
    ranking = rank(original,kernels,pending)
    by_index = {leaf["index"]:leaf for leaf in pending}
    nodes,ledger = deepcopy(seed["nodes"]),deepcopy(seed["arithmetic_ledger"])
    cache,results,new = {},[],[]
    print(json.dumps({
        "actual_latest920_OPEN_source_reconstructed":True,"origin_branches":eligible,
        "first_sampled_rankings_NOT_proofs":[
            {"leaf":item["actual_prior_OPEN_leaf_index"],
             "score":item["both_branches_sampled_score_NOT_a_lower_bound"]}
            for item in ranking[:5]],
    }),flush=True)
    for number,ranked in enumerate(ranking[:args.limit],1):
        leaf = by_index[ranked["actual_prior_OPEN_leaf_index"]]
        lo,hi = list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))
        ref = [(a+b)/2 for a,b in zip(lo,hi)]
        energy.scalar.full.hull.quadratic.reference_gate(ref,lo,hi,original["matrix"])
        trials,proofs = [],[]
        for owner in eligible:
            choices = ranked["branch_parameter_suggestions"][owner]
            for choice in choices[:args.branch_tries]:
                support,ratio = choice["full_support_index"],F(choice["mu_over_physical_rod_weight_sum"])
                base = kernels[support]
                mu = ratio*F(sum(base["weights"]),base["scale"])
                key = support,owner,mu
                if key not in cache:
                    cache[key] = energy.origin.kernel_gate(base,path,owner,mu)
                kernel = cache[key]
                certificate,result,numerical = energy.suggest(
                    kernel,original["matrix"],lo,hi,ref,original["radius"],arcs,args.parts)
                strict = result is not None and result["arithmetic_strict_entire_origin_branch"] is True
                trial = {
                    "origin_center_label":owner,"base_full_support_index":support,
                    "origin_multiplier":str(mu),"mu_over_physical_rod_weight_sum":str(ratio),
                    "certificate":certificate,"arithmetic_result":result,
                    "numerical_suggestions_NOT_proofs":numerical,
                    "whole_actual_closed_origin_branch_strict":strict,
                }
                trials.append(trial)
                print(json.dumps({"actual_prior_OPEN_leaf":leaf["index"],"origin_center":owner,
                                  "strict_whole_branch":strict,
                                  "exact_margin_display":float(F(result["strict_energy_margin"])) if result else None,
                                  "whole_leaf_requires_BOTH_branches":True}),flush=True)
                if strict:
                    proofs.append(trial)
                    break
        strict = {proof["origin_center_label"] for proof in proofs} == set(eligible)
        item = {"actual_prior_OPEN_leaf":leaf,"all_actual_branch_trials":trials,
                "strict_origin_branch_proofs":proofs,"both_entire_origin_branches_strict":strict}
        results.append(item)
        if strict:
            if nodes[leaf["index"]] != {"kind":"OPEN"}:
                raise ValueError("two-origin experiment would re-pay an old strict leaf")
            node_proofs = [{
                "origin_center_label":proof["origin_center_label"],
                "base_full_support_index":proof["base_full_support_index"],
                "origin_multiplier":proof["origin_multiplier"],"certificate":proof["certificate"],
            } for proof in proofs]
            nodes[leaf["index"]] = {"kind":KIND,"origin_branch_certificates":node_proofs}
            ledger.append({**leaf,"kind":KIND,"origin_branch_proofs":proofs})
            new.append(item)
        print(json.dumps({"two_origin_whole_leaf_checks":number,"of":args.limit,
                          "new_BOTH_branch_whole_leaves":len(new),
                          "formal_geometric_payments":0}),flush=True)
    ledger.sort(key=lambda leaf:leaf["index"])
    remaining = [leaf for leaf in pending if nodes[leaf["index"]] == {"kind":"OPEN"}]
    record = {"nodes":nodes,"alternative_supports":seed["alternative_supports"],
              "full134rod_supports":seed["full134rod_supports"],"arithmetic_ledger":ledger}
    retained = source.original_source.mixed.retention_gate(seed,record)
    if len(new)+len(remaining) != 920:
        raise ValueError("two-origin successor lost an unresolved domain or counted one branch as a leaf")
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("two-origin actual input changed during whole-branch arithmetic")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_source_closed_box":row,
        "source_file_sha256":seed["source_file_sha256"],
        "actual_checked920_predecessor_sha256":source.SEED_SHA,
        "actual_checked920_predecessor_controls_sha256":source.CONTROL_SHA,
        "actual_origin_eligible_original_center_labels":eligible,
        "numerical_all920_two_branch_ranking_NOT_lower_bounds":ranking,
        "all_actual_leaf_origin_branch_trials":results,
        "new_actual_whole_OPEN_leaves_with_BOTH_strict_branches":new,
        "new_strict_whole_old_OPEN_leaf_count":len(new),"remaining_OPEN_leaf_count":len(remaining),
        **record,"pending_closed_leaf_boxes":remaining,
        "prior_nodes_supports_AND580_strict_ledger_rows_preserved":list(retained),
        "all_previous64_whole_v4_OPEN_payments_retained_NOT_repeated":True,
        "both_closed_origin_branches_equality_and_overlap_retained":True,
        "old_arithmetic_qualified_REUSE_NOT_fresh_all_prior_leaf_replay":True,
        "all_NEW_whole_origin_branch_bounds_freshly_computed":True,
        "distinct_origin_mode_NOT_relabelled_as_old134_or92_kernel":True,
        "new_independent_branch_arithmetic_and_retention_controls_STILL_required":True,
        "entire_latest_source_model_history_geometry_admission_NOT_performed":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "actual_two_origin_branch_whole_leaf_arithmetic_completed_NOT_admission":True,
        "new_BOTH_branch_whole_leaves":len(new),"remaining_OPEN":len(remaining),
        "all_prior580_strict_ledger_rows_retained":True,"global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
