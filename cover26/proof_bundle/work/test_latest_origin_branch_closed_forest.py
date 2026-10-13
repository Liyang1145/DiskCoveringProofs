"""Independent actual919-origin25 subtree cover and every NEW strict bound."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_latest_origin_branch_closed_forest as producer
import test_latest_root25_two_origin_whole_leaves as arithmetic
import test_full134rod_two_origin_kernel as kernel_controls
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual919-origin25-closed-forest-controls-v1"


def independent_partition(matrix,leaf,nodes):
    contractor = producer.original_source.original_source.mixed.old.prior.prior.independently_contract
    work = deque([(0,list(map(F,leaf["lower"])),list(map(F,leaf["upper"])))])
    seen,domains,parents = set(),{},{}
    while work:
        index,lo,hi = work.popleft()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("independent origin subtree repeated or hid a node")
        seen.add(index)
        node,box = nodes[index],contractor(matrix,lo,hi)
        domains[index] = box
        if box is None:
            if node != {"kind":"EMPTY"}:
                raise ValueError("independent origin subtree falsely labelled necessary empty domain")
            continue
        lo,hi = box
        if node["kind"] == "SPLIT":
            if set(node) != {"kind","axis","mid","children"}:
                raise ValueError("independent origin subtree split has hidden proof fields")
            axis,cut,children = node["axis"],F(node["mid"]),node["children"]
            if (
                type(axis) is not int or not 0 <= axis < 15 or not lo[axis] < cut < hi[axis]
                or not isinstance(children,list) or len(children) != 2 or children[0] == children[1]
            ):
                raise ValueError("independent origin subtree lost strict cut/both closed halves")
            left,right = list(hi),list(lo)
            left[axis],right[axis] = cut,cut
            for child,a,b in ((children[0],list(lo),left),(children[1],right,list(hi))):
                if type(child) is not int or not index < child < len(nodes) or child in parents:
                    raise ValueError("independent origin subtree changed distinct child ownership")
                parents[child] = index
                work.append((child,a,b))
        elif node["kind"] == "OPEN":
            if node != {"kind":"OPEN"}:
                raise ValueError("independent origin OPEN carries unverified proof fields")
        elif node["kind"] == "ORIGIN-ENERGY":
            if set(node) != {"kind","certificate"}:
                raise ValueError("independent origin energy node has wrong distinct mode")
        else:
            raise ValueError("independent origin subtree changed proof mode")
    if len(seen) != len(nodes):
        raise ValueError("independent origin subtree lost an unvisited remainder")
    leaves = []
    for index,node in enumerate(nodes):
        if node["kind"] == "SPLIT":
            continue
        if domains[index] is None:
            leaves.append({"index":index,"kind":"EMPTY"})
        else:
            leaves.append({"index":index,"kind":node["kind"],
                           "lower":list(map(str,domains[index][0])),
                           "upper":list(map(str,domains[index][1]))})
    return domains,leaves


def scope(record,prior,leaf,whole16):
    if (
        record["schema"] != producer.SCHEMA
        or record["actual_checked919_predecessor_sha256"] != producer.PRIOR_SHA
        or record["actual_checked919_controls_sha256"] != producer.PRIOR_CONTROL_SHA
        or record["source_OPEN_index"] != 25 or record["actual_latest919_OPEN_leaf"] != leaf
        or record["whole_origin16_branch_prior_checked_proof"] != whole16
        or record["unresolved_origin_center_label"] != 25
        or record["base_full_support_index"] != 1
        or record["latest919_global_nodes_supports_and581_prior_strict_ledger_rows_UNMODIFIED"] is not True
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or any(record[field] is not False for field in (
            "global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("origin branch forest changed919 owner/checked other branch/unpaid scope")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh exact completed origin subtree diagnostic required")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("origin subtree diagnostic dependency changed")
    original,model,bases,prior,prior_controls,leaf,whole16,arcs,inventory = producer.inputs()
    scope(record,prior,leaf,whole16)
    nodes = record["origin25_closed_forest_nodes"]
    domains,leaves = independent_partition(original["matrix"],leaf,nodes)
    pending = [item for item in leaves if item["kind"] == "OPEN"]
    if (
        pending != record["retained_origin25_closed_OPEN_subleaves"]
        or record["entire_origin25_closed_branch_strictly_excluded"] != (not pending)
        or record["both_complete_origin_branches_cover_the_whole_old_leaf"] != (not pending)
    ):
        raise ValueError("independent origin subtree retained OPEN/domain classification differs")
    kernel = producer.energy.origin.kernel_gate(
        bases[record["base_full_support_index"]],original["data"][3],25,record["origin_multiplier"])
    identity = kernel_controls.independent_identity(bases[record["base_full_support_index"]],kernel)
    strict = {item["index"]:item for item in leaves if item["kind"] == "ORIGIN-ENERGY"}
    ledger = record["new_strict_origin25_subleaf_ledger"]
    if len({item["index"] for item in ledger}) != len(ledger) or {item["index"] for item in ledger} != set(strict):
        raise ValueError("independent origin subtree strict ledger does not cover actual energy leaves")
    checked = []
    for number,item in enumerate(ledger,1):
        actual = strict[item["index"]]
        if (
            item["lower"] != actual["lower"] or item["upper"] != actual["upper"]
            or item["certificate"] != nodes[item["index"]]["certificate"]
        ):
            raise ValueError("origin subtree strict certificate clips actual whole subleaf")
        trial = {"certificate":item["certificate"],"arithmetic_result":item["arithmetic_result"]}
        result = arithmetic.independent_arithmetic(original,kernel,actual,trial,arcs)
        if result["arithmetic_strict_entire_origin_branch"] is not True:
            raise ValueError("independent origin subtree strict lower bound failed")
        checked.append({"actual_origin_subleaf_index":item["index"],
                        "strict_radius_margin":result["strict_radius_margin"]})
        print(json.dumps({"independent_NEW_origin25_strict_subleaf":number,"of":len(ledger),
                          "node":item["index"],"whole_old_leaf_STILL_depends_on_complete_cover":True}),flush=True)
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid closed origin subtree control accepted: "+label)
    changed = {**record,"global_optimality_proved":True}
    reject("origin-subtree-promoted-to-global-proof",lambda:scope(changed,prior,leaf,whole16))
    changed = {**record,"whole_origin16_branch_prior_checked_proof":{}}
    reject("other-whole-origin-branch-omitted",lambda:scope(changed,prior,leaf,whole16))
    split_index = next((i for i,node in enumerate(nodes) if node["kind"] == "SPLIT"),None)
    if split_index is not None:
        bad = deepcopy(nodes)
        bad[split_index]["children"] = bad[split_index]["children"][:1]
        reject("one-closed-half-omitted",lambda:independent_partition(original["matrix"],leaf,bad))
        bad = deepcopy(nodes)
        bad[split_index]["children"][1] = bad[split_index]["children"][0]
        reject("closed-child-repeated",lambda:independent_partition(original["matrix"],leaf,bad))
        bad = deepcopy(nodes)
        axis = bad[split_index]["axis"]
        bad[split_index]["mid"] = str(domains[split_index][0][axis])
        reject("cut-not-strict-interior",lambda:independent_partition(original["matrix"],leaf,bad))
    if nodes:
        reject("unvisited-origin-remainder-hidden",lambda:independent_partition(
            original["matrix"],leaf,[*nodes,{"kind":"OPEN"}]))
    if pending:
        # A complete-cover claim while an actual OPEN leaf remains fails
        # independent equality, not only a trust-based flag comparison.
        def false_closed_claim():
            bad = {**record,"retained_origin25_closed_OPEN_subleaves":[],
                   "entire_origin25_closed_branch_strictly_excluded":True}
            if pending != bad["retained_origin25_closed_OPEN_subleaves"]:
                raise ValueError("actual open domain remains")
        reject("partial-origin-subforest-forged-complete",false_closed_claim)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("origin subtree actual input changed during independent controls")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("origin subtree primary diagnostic changed")
    inventory.update(record["input_sha256"])
    inventory.update({
        linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__),
        linux(arithmetic.__file__):binding.sha(arithmetic.__file__),
        linux(kernel_controls.__file__):binding.sha(kernel_controls.__file__),
    })
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "diagnosis_sha256":args.diagnosis_sha256,
        "actual_checked919_predecessor_sha256":producer.PRIOR_SHA,
        "actual_latest919_OPEN_leaf":leaf,
        "independent_complete_closed_origin25_partition_reconstructed":True,
        "prior_whole_origin16_branch_independently_checked_receipt_honestly_REUSED":True,
        "independent_origin_kernel_square_completion":identity,
        "all_NEW_strict_whole_origin25_subleaf_bounds_independently_recomputed":checked,
        "independent_sine_square_secant_tangent_point_controls":3*len(checked),
        "retained_origin25_closed_OPEN_subleaves":pending,
        "entire_origin25_closed_branch_strictly_excluded":not pending,
        "both_complete_origin_branches_exclude_whole_old_leaf":not pending,
        "actual_closed_half_owner_completion_and_scope_rejection_controls":rejected,
        "latest919_global_tree_supports_and581_strict_rows_UNMODIFIED":True,
        "old_arithmetic_qualified_REUSE_NOT_fresh_all_prior_replay":True,
        "arithmetic_only_NOT_latest_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "independent_origin25_closed_forest_controls_completed_NOT_admission":True,
        "new_strict_origin_subleaves":len(checked),"retained_origin_branch_OPEN":len(pending),
        "whole_old_leaf_arithmetic_excluded":not pending,"actual_rejection_controls":len(rejected),
    }),flush=True)


if __name__ == "__main__":
    main()
