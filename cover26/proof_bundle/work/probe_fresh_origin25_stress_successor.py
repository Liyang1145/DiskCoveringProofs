"""Fresh origin-constrained stresses for ONLY the two checked OPEN subleaves.

Preserves latest919 global source and15-node partial tree/6strict ledger.
Numerical stresses suggest fresh kernels; exact whole-domain bounds decide.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import lsq_linear
from sympy import Matrix

from audit_prefix_partition import linux
import probe_remaining_origin25_primal_relaxation as source
import n26_origin_branch_correlated_energy as energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest-origin25-fresh-positive-stress-retained-successor-v1"
KIND = "FRESH-FULL134-ORIGIN25-ENERGY"
PRIMAL = Path("outputs/n26-actual-two-origin25-OPEN-primal-relaxation-diagnostic-v1.json")
PRIMAL_CONTROLS = Path("outputs/n26-actual-two-origin25-OPEN-primal-relaxation-independent-controls-v1.json")
PRIMAL_SHA = "f6a823d876eea8547bae03afeeca9d65d267daf97e0586c3a5b4ac9416b01793"


def inputs():
    original,model,bases,seed,pending,arcs,inventory = source.inputs()
    if binding.sha(PRIMAL) != PRIMAL_SHA:
        raise ValueError("fresh origin stress changed actual prior primal diagnostic")
    primal,controls = binding.read(PRIMAL),binding.read(PRIMAL_CONTROLS)
    if (
        controls["schema"] != "N26-independent-actual-retained-origin25-primal-relaxation-controls-v1"
        or controls["diagnosis_sha256"] != PRIMAL_SHA
        or controls["actual_retained_origin25_below_root_necessary_model_realizations"] != 0
        or primal["actual_partial_branch_diagnosis_sha256"] != source.SEED_SHA
        or primal["actual_partial_branch_controls_sha256"] != source.CONTROL_SHA
        or any(record["verified"] is not False or record["new_geometric_payments"] != 0
               or record["global_optimality_proved"] is not False for record in (primal,controls))
    ):
        raise ValueError("fresh origin stress lost checked actual primal failure scope/branch ancestry")
    for record in (primal,controls):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("fresh origin stress actual checked primal input changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("fresh origin stress original input digest conflict")
            inventory[text] = digest
    inventory.update({
        linux(PRIMAL):PRIMAL_SHA,linux(PRIMAL_CONTROLS):binding.sha(PRIMAL_CONTROLS),
        linux(__file__):binding.sha(__file__),
        linux("work/n26-fresh-origin25-stress-successor-proof.md"):binding.sha(
            "work/n26-fresh-origin25-stress-successor-proof.md"),
    })
    return original,model,bases,seed,pending,primal,arcs,inventory


def fresh_weights(model,item):
    turns = list(map(F,item["actual_fixed_feasible_anchor_turns"]))
    anchors = np.array([[np.cos(2*np.pi*float(t)),np.sin(2*np.pi*float(t))] for t in [F(0),*turns]])
    free = np.array([[float(F(value)) for value in point] for point in item["rational60_free_points"]])
    positions = np.vstack((anchors,free))
    matrix = np.zeros((120,135))
    squared = []
    for index,(u,v) in enumerate(model["edges"]):
        delta = positions[u]-positions[v]
        squared.append(float(delta@delta))
        if u >= 16:
            matrix[2*(u-16):2*(u-16)+2,index] += 2*delta
        if v >= 16:
            matrix[2*(v-16):2*(v-16)+2,index] -= 2*delta
    squared.append(float(free[25]@free[25]))
    matrix[50:52,134] = 2*free[25]
    squared = np.array(squared)
    active = max(squared)-squared <= 1e-7
    optimized = lsq_linear(
        np.vstack((matrix,np.ones(135))),np.r_[np.zeros(120),1.],
        bounds=(np.full(135,1e-13),np.where(active,1.,1e-8)),
        method="trf",tol=1e-13,max_iter=500)
    weights = np.maximum(optimized.x,1e-13)
    weights /= weights.sum()
    return weights[:134],weights[134],{
        "numerical_positive_stress_fit_success_NOT_proof":bool(optimized.success),
        "numerical_active_physical_and_origin_constraints":int(active.sum()),
        "numerical_free_equilibrium_residual_NOT_proof":float(max(abs(matrix@weights))),
        "numerical_total_weight_NOT_proof":float(weights.sum()),
        "origin_multiplier_is_NOT_a_physical135th_rod":True,
    }


def exact_base(model,weights):
    full = energy.scalar.full
    scale = 10**30
    integers = [max(1,round(float(value)*scale)) for value in weights]
    laplacian = full.direct.laplacian(model["edges"],integers,vertices=76)
    inverse,denominator = Matrix([row[16:] for row in laplacian[16:]]).to_DM().inv_den()
    values = [[int(value) for value in row] for row in inverse.to_Matrix().tolist()]
    den = int(denominator)
    if den < 0:
        den,values = -den,[[-value for value in row] for row in values]
    certificate = {
        "schema":full.SCHEMA,"mode":full.MODE,"weight_scale":scale,"weight_numerators":integers,
        "inverse_denominator":str(den),"inverse_numerators":[list(map(str,row)) for row in values],
    }
    return certificate,full.kernel_gate(model,certificate)


def branch_domains(original,seed,nodes):
    prior = source.source
    mixed = prior.original_source.original_source.mixed
    view = [{"kind":"OPEN"} if node["kind"] == KIND else deepcopy(node) for node in nodes]
    a = prior.domains(original["matrix"],seed["actual_latest919_OPEN_leaf"],view,
                      mixed.old.prior.prior.tighten,False)
    b = prior.domains(original["matrix"],seed["actual_latest919_OPEN_leaf"],view,
                      mixed.old.prior.prior.independently_contract,True)
    for result in (a,b):
        for leaf in result:
            if nodes[leaf["index"]]["kind"] == KIND:
                leaf["kind"] = KIND
    if a != b:
        raise ValueError("fresh origin successor changed complete actual closed branch domains")
    return a


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve fresh origin stress arithmetic successor")
    original,model,bases,seed,pending,primal,arcs,inventory = inputs()
    by_index = {item["actual_retained_origin25_OPEN_subleaf"]["index"]:item for item in primal["results"]}
    nodes,ledger = deepcopy(seed["origin25_closed_forest_nodes"]),deepcopy(seed["new_strict_origin25_subleaf_ledger"])
    supports,targets,results = [],[],[]
    for leaf in pending:
        item = by_index[leaf["index"]]
        weights,mu,numerical = fresh_weights(model,item)
        certificate,base = exact_base(model,weights)
        multiplier = F(max(0,round(float(mu)*10**30)),10**30)
        kernel = energy.origin.kernel_gate(base,original["data"][3],25,multiplier)
        turns = list(map(F,item["actual_fixed_feasible_anchor_turns"]))
        exact_certificate,result,choices = energy.suggest(
            kernel,original["matrix"],list(map(F,leaf["lower"])),list(map(F,leaf["upper"])),
            turns,original["radius"],arcs,16)
        strict = result is not None and result["arithmetic_strict_entire_origin_branch"] is True
        trial = {
            "actual_latest_origin25_OPEN_subleaf":leaf,
            "fresh_positive134rod_kernel_certificate":certificate,
            "fresh_origin_multiplier":str(multiplier),
            "whole_subleaf_origin_certificate":exact_certificate,
            "whole_subleaf_origin_arithmetic_result":result,
            "fresh_actual_whole_subleaf_strict":strict,
            "numerical_stress_suggestion_NOT_proof":numerical,
            "numerical_curvature_suggestion_NOT_proof":choices,
        }
        results.append(trial)
        if strict:
            support_index = len(supports)
            supports.append({"base_kernel_certificate":certificate,"origin_multiplier":str(multiplier)})
            if nodes[leaf["index"]] != {"kind":"OPEN"}:
                raise ValueError("fresh origin successor reset a previous nonOPEN branch leaf")
            nodes[leaf["index"]] = {
                "kind":KIND,"fresh_support_index":support_index,"certificate":exact_certificate}
            target = {**leaf,"kind":KIND,"fresh_support_index":support_index,
                      "certificate":exact_certificate,"arithmetic_result":result}
            ledger.append(target)
            targets.append(target)
        print(json.dumps({
            "actual_retained_origin25_subleaf":leaf["index"],
            "fresh_exact_whole_origin25_subleaf_strict":strict,
            "exact_margin_display":float(F(result["strict_energy_margin"])) if result else None,
            "origin_mu_display":float(multiplier),"formal_geometric_payments":0,
        }),flush=True)
    actual = branch_domains(original,seed,nodes)
    remaining = [leaf for leaf in actual if leaf["kind"] == "OPEN"]
    ledger.sort(key=lambda leaf:leaf["index"])
    old = {leaf["index"]:leaf for leaf in seed["new_strict_origin25_subleaf_ledger"]}
    new = {leaf["index"]:leaf for leaf in ledger}
    if (
        len(nodes) != len(seed["origin25_closed_forest_nodes"])
        or any(node["kind"] != "OPEN" and nodes[i] != node
               for i,node in enumerate(seed["origin25_closed_forest_nodes"]))
        or any(new.get(index) != leaf for index,leaf in old.items())
        or len(targets)+len(remaining) != len(pending)
    ):
        raise ValueError("fresh origin successor lost old6strict proofs or unchecked whole domains")
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("fresh origin positive stress source changed during exact calculation")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_prior_whole_leaf":seed["actual_latest919_OPEN_leaf"],
        "actual_checked_partial_origin25_seed_sha256":source.SEED_SHA,
        "actual_checked_partial_origin25_controls_sha256":source.CONTROL_SHA,
        "actual_latest919_global_predecessor_sha256":source.source.PRIOR_SHA,
        "whole_origin16_branch_prior_checked_proof":seed["whole_origin16_branch_prior_checked_proof"],
        "origin25_closed_forest_nodes":nodes,"fresh_positive_origin25_supports":supports,
        "actual_fresh_stress_trials":results,"new_strict_origin25_subleaf_targets":targets,
        "strict_origin25_subleaf_ledger":ledger,"retained_origin25_OPEN_subleaves":remaining,
        "all_old15_nodes_and6strict_partial_ledgers_preserved":True,
        "no_extra_split_or_proper_subbox_called_whole_old_OPEN_subleaf":True,
        "entire_origin25_branch_strictly_excluded":not remaining,
        "both_checked_origin_branches_arithmetically_exclude_whole_leaf2641":not remaining,
        "latest919_global_tree_and581prior_strict_ledger_rows_UNMODIFIED":True,
        "old_checked_whole_and_partial_arithmetic_qualified_REUSE_NOT_replayed":True,
        "new_independent_fresh_kernel_origin_arithmetic_and_retention_controls_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "fresh_origin25_stress_successor_arithmetic_completed_NOT_admission":True,
        "new_whole_partial_OPEN_subleaves":len(targets),"remaining_origin25_OPEN":len(remaining),
        "whole_old_leaf2641_arithmetic_excluded":not remaining,"formal_geometric_payments":0,
    }),flush=True)


if __name__ == "__main__":
    main()
