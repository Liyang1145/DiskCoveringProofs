"""Retain checked919 source; refine ONLY the unresolved origin branch.

Closed branch trees are diagnostic arithmetic, not new global model labels.
The successful prior whole branch and all previous complete-leaf payments
are qualified checked reuse; newly introduced strict subleaf bounds are fresh.
"""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest_root25_origin_source as original_source
import n26_origin_branch_correlated_energy as energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-actual919-retained-origin-branch-closed-forest-diagnostic-v1"
PRIOR = Path("outputs/n26-root25-latest920-two-origin-whole-leaf-diagnostic-v1.json")
PRIOR_CONTROL = Path("outputs/n26-root25-latest920-two-origin-whole-leaf-independent-controls-v1.json")
PRIOR_SHA = "3889054d0b151b4daa951c0dd9553fed78facf415229e75be075221ccc3634b8"
PRIOR_CONTROL_SHA = "6919a00fd5885f1bc4f5138fb84ff96dc9e4cb46762b74e89f2f6fc63231dab2"


def inputs():
    original,model,bases,seed920,controls920,row,pending920,arcs,inventory = original_source.source()
    if binding.sha(PRIOR) != PRIOR_SHA or binding.sha(PRIOR_CONTROL) != PRIOR_CONTROL_SHA:
        raise ValueError("origin branch refinement needs the actual completed919 pair")
    prior,controls = binding.read(PRIOR),binding.read(PRIOR_CONTROL)
    if (
        controls["diagnosis_sha256"] != PRIOR_SHA or prior["remaining_OPEN_leaf_count"] != 919
        or controls["remaining_OPEN_leaf_count"] != 919
        or prior["actual_source_closed_box"] != row
        or prior["source_file_sha256"] != seed920["source_file_sha256"]
        or prior["new_strict_whole_old_OPEN_leaf_count"] != 1
        or controls["new_strict_whole_old_OPEN_leaf_count"] != 1
        or any(record["verified"] is not False or record["new_geometric_payments"] != 0
               or record["global_optimality_proved"] is not False for record in (prior,controls))
    ):
        raise ValueError("branch forest changed qualified predecessor owner/status")
    for record in (prior,controls):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("branch forest checked predecessor dependency changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("branch forest original-model dependency identity conflict")
            inventory[text] = digest
    pending = prior["pending_closed_leaf_boxes"]
    by920 = {leaf["index"]:leaf for leaf in pending920}
    if len(pending) != 919 or any(by920.get(leaf["index"]) != leaf for leaf in pending):
        raise ValueError("branch forest reset the latest919 retained domains")
    target = next(item for item in prior["all_actual_leaf_origin_branch_trials"]
                  if item["actual_prior_OPEN_leaf"]["index"] == 2641)
    leaf = target["actual_prior_OPEN_leaf"]
    if leaf not in pending or target["both_entire_origin_branches_strict"]:
        raise ValueError("branch forest selected a prior paid/changed source leaf")
    proofs = target["strict_origin_branch_proofs"]
    if len(proofs) != 1 or proofs[0]["origin_center_label"] != 16:
        raise ValueError("this branch refinement must preserve actual checked whole owner16 proof")
    inventory.update({
        linux(PRIOR):PRIOR_SHA,linux(PRIOR_CONTROL):PRIOR_CONTROL_SHA,
        linux(__file__):binding.sha(__file__),
        linux("work/n26-origin-branch-closed-forest-proof.md"):binding.sha(
            "work/n26-origin-branch-closed-forest-proof.md"),
    })
    return original,model,bases,prior,controls,leaf,proofs[0],arcs,inventory


def split_nodes(node,index,lower,upper,total):
    axis,cut,children = node["axis"],F(node["mid"]),node["children"]
    if (
        set(node) != {"kind","axis","mid","children"} or type(axis) is not int
        or not 0 <= axis < 15 or not lower[axis] < cut < upper[axis]
        or len(children) != 2 or children[0] == children[1]
        or any(type(child) is not int or not index < child < total for child in children)
    ):
        raise ValueError("origin branch split lost a strict closed half/shared endpoint")
    left,right = list(upper),list(lower)
    left[axis],right[axis] = cut,cut
    return ((children[0],list(lower),left),(children[1],right,list(upper)))


def domains(matrix,leaf,nodes,contractor,breadth_first):
    work = deque([(0,list(map(F,leaf["lower"])),list(map(F,leaf["upper"])))])
    seen,result = set(),[]
    while work:
        index,lo,hi = work.popleft() if breadth_first else work.pop()
        if index in seen or not 0 <= index < len(nodes):
            raise ValueError("branch forest has repeated or hidden domain")
        seen.add(index)
        box = contractor(matrix,lo,hi)
        node = nodes[index]
        if box is None:
            if node != {"kind":"EMPTY"}:
                raise ValueError("branch forest changed an exact empty closed domain")
            result.append({"index":index,"kind":"EMPTY"})
        elif node["kind"] == "SPLIT":
            children = split_nodes(node,index,*box,len(nodes))
            work.extend(children if breadth_first else reversed(children))
        elif node["kind"] in ("OPEN","ORIGIN-ENERGY"):
            result.append({"index":index,"kind":node["kind"],
                           "lower":list(map(str,box[0])),"upper":list(map(str,box[1]))})
        else:
            raise ValueError("branch forest has an invalid proof mode")
    if len(seen) != len(nodes):
        raise ValueError("branch forest has an unreachable remainder")
    return sorted(result,key=lambda row:row["index"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--checks",type=int,default=32)
    parser.add_argument("--depth",type=int,default=6)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.checks <= 1024 or not 0 <= args.depth <= 20:
        raise ValueError("branch forest needs fresh report and bounded complete retention")
    original,model,bases,prior,controls,leaf,whole16,arcs,inventory = inputs()
    source = original_source.original_source.mixed
    contractor,other = source.old.prior.prior.tighten,source.old.prior.prior.independently_contract
    support,owner,mu = 1,25,F(1,10000)*F(sum(bases[1]["weights"]),bases[1]["scale"])
    kernel = energy.origin.kernel_gate(bases[support],original["data"][3],owner,mu)
    nodes,ledger,attempts = [{"kind":"OPEN"}],[],[]
    work = deque([(0,list(map(F,leaf["lower"])),list(map(F,leaf["upper"])),0)])
    checks = 0
    while work and checks < args.checks:
        index,lo,hi,depth = work.popleft()
        box = contractor(original["matrix"],lo,hi)
        independent = other(original["matrix"],lo,hi)
        if box != independent:
            raise ValueError("origin branch closed contraction disagrees")
        if box is None:
            nodes[index] = {"kind":"EMPTY"}
            continue
        lo,hi = box
        checks += 1
        # Preserve already independently failed original whole-branch
        # arithmetic as a split suggestion; do not recompute it unchanged.
        if index == 0:
            old = next(trial for item in prior["all_actual_leaf_origin_branch_trials"]
                       if item["actual_prior_OPEN_leaf"]["index"] == 2641
                       for trial in item["all_actual_branch_trials"]
                       if trial["origin_center_label"] == 25
                       and F(trial["mu_over_physical_rod_weight_sum"]) == F(1,10000))
            certificate,result = old["certificate"],old["arithmetic_result"]
            choices = {"actual_failed_parent_branch_REUSED_NOT_recomputed":True}
        else:
            reference = [(a+b)/2 for a,b in zip(lo,hi)]
            certificate,result,choices = energy.suggest(
                kernel,original["matrix"],lo,hi,reference,original["radius"],arcs,8)
        strict = result is not None and result["arithmetic_strict_entire_origin_branch"] is True
        attempts.append({"actual_branch_node":index,"closed_lower":list(map(str,lo)),
                         "closed_upper":list(map(str,hi)),"certificate":certificate,
                         "arithmetic_result":result,"numerical_suggestions_NOT_proofs":choices,
                         "fresh_strict_closed_origin_subleaf":strict})
        if strict:
            nodes[index] = {"kind":"ORIGIN-ENERGY","certificate":certificate}
            ledger.append({"index":index,"kind":"ORIGIN-ENERGY","lower":list(map(str,lo)),
                           "upper":list(map(str,hi)),"certificate":certificate,"arithmetic_result":result})
        elif depth < args.depth:
            eligible = [axis for axis,(a,b) in enumerate(zip(lo,hi)) if a < b]
            if eligible:
                diagonal = list(map(F,certificate["curvature_correction"])) if certificate else [F(1)]*15
                axis = max(eligible,key=lambda axis:(diagonal[axis]*(hi[axis]-lo[axis])**2,hi[axis]-lo[axis],-axis))
                cut,children = (lo[axis]+hi[axis])/2,[len(nodes),len(nodes)+1]
                nodes.extend(({"kind":"OPEN"},{"kind":"OPEN"}))
                nodes[index] = {"kind":"SPLIT","axis":axis,"mid":str(cut),"children":children}
                left,right = list(hi),list(lo)
                left[axis],right[axis] = cut,cut
                work.extend(((children[0],list(lo),left,depth+1),(children[1],right,list(hi),depth+1)))
        print(json.dumps({"actual_origin25_branch_forest_check":checks,"node":index,
                          "depth":depth,"strict_closed_subleaf":strict,
                          "strict_subleaves":len(ledger),"nodes":len(nodes),
                          "whole_old_leaf_NOT_paid_until_all_branch_OPEN_gone":True}),flush=True)
    actual = domains(original["matrix"],leaf,nodes,contractor,False)
    independent = domains(original["matrix"],leaf,nodes,other,True)
    if actual != independent:
        raise ValueError("both whole branch trees/shared boundaries did not reconstruct")
    pending = [row for row in actual if row["kind"] == "OPEN"]
    strict_indices = {row["index"] for row in actual if row["kind"] == "ORIGIN-ENERGY"}
    if strict_indices != {row["index"] for row in ledger}:
        raise ValueError("branch forest new strict leaf ledger incomplete")
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("origin branch refinement changed an actual input")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_checked919_predecessor_sha256":PRIOR_SHA,
        "actual_checked919_controls_sha256":PRIOR_CONTROL_SHA,
        "actual_latest919_OPEN_leaf":leaf,"whole_origin16_branch_prior_checked_proof":whole16,
        "unresolved_origin_center_label":owner,"base_full_support_index":support,"origin_multiplier":str(mu),
        "origin25_closed_forest_nodes":nodes,"all_actual_branch_trials":attempts,
        "new_strict_origin25_subleaf_ledger":sorted(ledger,key=lambda row:row["index"]),
        "retained_origin25_closed_OPEN_subleaves":pending,
        "entire_origin25_closed_branch_strictly_excluded":not pending,
        "both_complete_origin_branches_cover_the_whole_old_leaf":not pending,
        "all_shared_closed_cut_boundaries_and_unvisited_remainders_retained":True,
        "latest919_global_nodes_supports_and581_prior_strict_ledger_rows_UNMODIFIED":True,
        "checked_whole_origin16_branch_and_failed_parent25_arithmetic_qualified_REUSE":True,
        "new_independent_subleaf_arithmetic_and_complete_branch_controls_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"actual_unresolved_origin_branch_forest_arithmetic_completed_NOT_admission":True,
                      "strict_origin25_subleaves":len(ledger),"retained_branch_OPEN":len(pending),
                      "whole_old_leaf_arithmetic_excluded":not pending,"formal_geometric_payments":0}),flush=True)


if __name__ == "__main__":
    main()
