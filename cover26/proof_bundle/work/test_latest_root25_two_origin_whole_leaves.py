"""Independent NEW origin calculus, full two-branch coverage and920 retention."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_origin_branch_correlated_energy as energy
import n26_latest_root25_origin_source as source
import probe_latest_root25_two_origin_whole_leaves as producer
import test_full134rod_two_origin_kernel as independent_kernel
import test_checked_root28_full134rod_intersections as domains
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-latest920-two-origin-whole-leaf-controls-v1"


def independent_arithmetic(original,kernel,leaf,trial,arcs):
    certificate = trial["certificate"]
    actual = energy.bound(kernel,original["matrix"],leaf["lower"],leaf["upper"],
                          certificate,original["radius"],arcs)
    if actual != trial["arithmetic_result"]:
        raise ValueError("actual distinct-origin whole-branch bound did not reconstruct")
    hull,quadratic = energy.scalar.full.hull,energy.scalar.full.hull.quadratic
    ref,lo,hi,_,_ = hull.hull_gate(certificate["reference_turns"],leaf["lower"],leaf["upper"],original["matrix"])
    parts = certificate["parts"]
    combined,total = [[F(0)]*15 for _ in range(15)],F(0)
    for index in range(parts):
        a,b = F(index,parts),F(index+1,parts)
        weight = F(2*parts-2*index-1,parts*parts)
        left,right = [],[]
        for r,x,y in zip(ref[1:],lo[1:],hi[1:]):
            values = (r+a*(x-r),r+a*(y-r),r+b*(x-r),r+b*(y-r))
            left.append(min(values))
            right.append(max(values))
        minorant = quadratic.hessian_minorant(kernel,original["matrix"],left,right,arcs)
        for i in range(15):
            for j in range(15):
                combined[i][j] += weight*minorant[i][j]
        total += weight
    if total != 1:
        raise ValueError("independent origin Taylor normalization failed")
    correction,z = list(map(F,certificate["curvature_correction"])),list(map(F,certificate["quadratic_support_point"]))
    allowance = F(15,quadratic.ROUND_GRID)
    Q = [[value+(correction[i]-allowance if i == j else 0)
          for j,value in enumerate(row)] for i,row in enumerate(combined)]
    pivots = quadratic.positive_ldl(Q)
    a,b = [x-r for x,r in zip(lo[1:],ref[1:])],[y-r for y,r in zip(hi[1:],ref[1:])]
    pair_energy,gradient = hull.outward_point_values(kernel,ref,arcs)
    mu,R = kernel["origin_multiplier"],kernel["original_physical_ground_resistance"]
    k = mu/(1+mu*R)
    reference_energy = pair_energy+k
    error = sum((high-low)*max(abs(x),abs(y))/2
                for (low,high),x,y in zip(gradient[1:],a,b))
    linear = [(low+high)/2-eta*(x+y)/2
              for (low,high),eta,x,y in zip(gradient[1:],correction,a,b)]
    constant = sum(eta*x*y/2 for eta,x,y in zip(correction,a,b))-error
    Qz = [sum(value*z[j] for j,value in enumerate(row)) for row in Q]
    tangent_at_z = sum(x*y for x,y in zip(z,Qz))/2
    divergence,dual_constant,seen = [F(0)]*16,F(0),set()
    denominator = certificate["difference_dual"]["q"]
    for i,j,encoded in certificate["difference_dual"]["terms"]:
        if (i,j) in seen or int(encoded) < 0 or denominator <= 0:
            raise ValueError("independent origin dual invalid")
        seen.add((i,j))
        weight = F(int(encoded),denominator)
        divergence[i] -= weight
        divergence[j] += weight
        dual_constant += weight*(ref[j]-ref[i]-F(original["matrix"][i][j],10**40))
    support = dual_constant+sum(min((p+q+d)*x,(p+q+d)*y)
                               for p,q,d,x,y in zip(linear,Qz,divergence[1:],a,b))
    lower = reference_energy+constant-tangent_at_z+support
    budget = kernel["original_physical_rod_weight_sum"]+mu
    upper = original["radius"]**2*budget
    square,grid = max(lower,F(0))/budget,10**100
    radius_lower = F(isqrt(square.numerator*grid*grid//square.denominator),grid)
    if (
        lower != F(actual["boundary_origin_branch_energy_lower"])
        or upper != F(actual["same_root_origin_branch_energy_upper"])
        or lower-upper != F(actual["strict_energy_margin"])
        or radius_lower-original["radius"] != F(actual["strict_radius_margin"])
        or allowance != F(actual["rounding_operator_error_charged"])
        or min(pivots) != F(actual["exact_positive_LDL_minimum_pivot"])
        or error != F(actual["outward_gradient_interval_error_charged"])
        or k != F(actual["boundary_origin_constant"])
    ):
        raise ValueError("independent origin constant/budget/Taylor/LDL/secant/tangent/dual calculation differs")
    point_lower,point_upper = energy.origin.point_interval(kernel,ref[1:],arcs)
    if reference_energy > point_upper or point_lower-reference_energy > F(1,10**80):
        raise ValueError("new origin point interval differs from outward reference energy")
    for point in (lo[1:],hi[1:],[(x+y)/2 for x,y in zip(lo[1:],hi[1:])]):
        angles = quadratic.reference_gate(point,lo[1:],hi[1:],original["matrix"])[0]
        numerator = 0
        for i,j,weight in kernel["pairs"]:
            _,sine = arcs.sincos_turn((angles[j]-angles[i])/2)
            numerator += 4*weight*max(sine[0]*sine[0],sine[1]*sine[1])
        upper_point = k+F(numerator,kernel["energy_denominator"]*arcs.SCALE**2)
        if lower > upper_point:
            raise AssertionError("origin whole-domain lower bound exceeds independent sine-square point upper")
        delta = [value-r for value,r in zip(point,ref[1:])]
        for d,eta,x,y in zip(delta,correction,a,b):
            gap = -eta*d*d/2-(-eta*(x+y)*d/2+eta*x*y/2)
            if gap != eta*(d-x)*(y-d)/2 or gap < 0:
                raise AssertionError("independent origin closed concave secant identity failed")
        displaced = [d-value for d,value in zip(delta,z)]
        positive = sum(displaced[i]*Q[i][j]*displaced[j] for i in range(15) for j in range(15))/2
        tangent_gap = sum(delta[i]*Q[i][j]*delta[j] for i in range(15) for j in range(15))/2
        tangent_gap -= sum(d*q for d,q in zip(delta,Qz))-tangent_at_z
        if positive != tangent_gap or positive < 0:
            raise AssertionError("independent origin positive-quadratic tangent identity failed")
    return actual


def retention(record,seed,pending):
    by_index = {leaf["index"]:leaf for leaf in pending}
    nodes,ledger = deepcopy(seed["nodes"]),deepcopy(seed["arithmetic_ledger"])
    seen = set()
    for target in record["new_actual_whole_OPEN_leaves_with_BOTH_strict_branches"]:
        leaf,index = target["actual_prior_OPEN_leaf"],target["actual_prior_OPEN_leaf"]["index"]
        proofs = target["strict_origin_branch_proofs"]
        if (
            index in seen or by_index.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"}
            or len(proofs) != 2 or {proof["origin_center_label"] for proof in proofs} != {16,25}
            or target["both_entire_origin_branches_strict"] is not True
        ):
            raise ValueError("two-origin payment changed an owner/domain or omitted one whole branch")
        seen.add(index)
        for proof in proofs:
            result = proof["arithmetic_result"]
            if (
                proof["whole_actual_closed_origin_branch_strict"] is not True
                or result["arithmetic_strict_entire_origin_branch"] is not True
                or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
            ):
                raise ValueError("two-origin payment contains a nonstrict branch")
        nodes[index] = {"kind":producer.KIND,"origin_branch_certificates":[{
            "origin_center_label":proof["origin_center_label"],
            "base_full_support_index":proof["base_full_support_index"],
            "origin_multiplier":proof["origin_multiplier"],"certificate":proof["certificate"],
        } for proof in proofs]}
        ledger.append({**leaf,"kind":producer.KIND,"origin_branch_proofs":proofs})
    ledger.sort(key=lambda leaf:leaf["index"])
    remaining = [leaf for leaf in pending if leaf["index"] not in seen]
    if (
        record["nodes"] != nodes or record["arithmetic_ledger"] != ledger
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["full134rod_supports"] != seed["full134rod_supports"]
        or record["pending_closed_leaf_boxes"] != remaining
        or record["new_strict_whole_old_OPEN_leaf_count"] != len(seen)
        or record["remaining_OPEN_leaf_count"] != len(remaining)
        or len(remaining)+len(seen) != 920
    ):
        raise ValueError("two-origin successor lost prior proof/support/closed OPEN remainder")
    return remaining


def root_positive(original,kernel):
    base = source.original_source.model_source.base
    geometry,_,_,_ = base.root_geometry(*original["data"][:3])
    lower = kernel["boundary_origin_constant"]
    for i,j,weight in kernel["pairs"]:
        dot = base.iv.add(base.iv.mul(geometry[i][0],geometry[j][0]),
                          base.iv.mul(geometry[i][1],geometry[j][1]))
        lower += F(2*weight,kernel["energy_denominator"])*(1-dot[1])
    cap = original["radius"]**2*kernel["radius_squared_budget_weight"]
    return lower <= cap


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("new exact completed two-origin diagnosis and fresh independent output required")
    record = binding.read(args.diagnosis)
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("two-origin primary selected dependency changed")
    original,model,bases,seed,prior_controls,row,pending,arcs,inventory = source.source()
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != row
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_checked920_predecessor_sha256"] != source.SEED_SHA
        or record["actual_checked920_predecessor_controls_sha256"] != source.CONTROL_SHA
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["actual_origin_eligible_original_center_labels"] != [16,25]
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or any(record[field] is not False for field in ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("independent two-origin whole-leaf scope/source/executor changed")
    remaining = retention(record,seed,pending)
    retained = source.original_source.mixed.retention_gate(seed,record)
    if list(retained) != record["prior_nodes_supports_AND580_strict_ledger_rows_preserved"]:
        raise ValueError("two-origin old proof/ledger retention count differs")
    before,parents = domains.all_domains(original,row,seed["nodes"])
    after,new_parents = domains.all_domains(original,row,record["nodes"])
    if before != after or parents != new_parents:
        raise ValueError("two-origin successor changed an old closed leaf/split/shared endpoint")
    by_index = {leaf["index"]:leaf for leaf in pending}
    kernels,identities,checked,strict_whole,seen = {},[],[],set(),set()
    for item in record["all_actual_leaf_origin_branch_trials"]:
        leaf,index = item["actual_prior_OPEN_leaf"],item["actual_prior_OPEN_leaf"]["index"]
        if index in seen or by_index.get(index) != leaf or before[index] != (
                list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))):
            raise ValueError("two-origin trials do not use actual unique entire latest OPEN domains")
        seen.add(index)
        strict,root_possible = set(),[]
        for trial in item["all_actual_branch_trials"]:
            owner,support,mu = trial["origin_center_label"],trial["base_full_support_index"],F(trial["origin_multiplier"])
            if owner not in (16,25) or type(support) is not int or not 0 <= support < len(bases):
                raise ValueError("two-origin actual trial has a wrong source support/owner")
            key = support,owner,mu
            if key not in kernels:
                kernels[key] = energy.origin.kernel_gate(bases[support],original["data"][3],owner,mu)
                identities.append(independent_kernel.independent_identity(bases[support],kernels[key]))
            kernel = kernels[key]
            if trial["certificate"] is None or trial["arithmetic_result"] is None:
                if trial["whole_actual_closed_origin_branch_strict"]:
                    raise ValueError("failed origin LDL attempt was promoted to a strict branch")
                continue
            result = independent_arithmetic(original,kernel,leaf,trial,arcs)
            if result["arithmetic_strict_entire_origin_branch"] != trial["whole_actual_closed_origin_branch_strict"]:
                raise ValueError("independent origin strict branch classification differs")
            if result["arithmetic_strict_entire_origin_branch"]:
                strict.add(owner)
            checked.append({"actual_prior_OPEN_leaf_index":index,"origin_center_label":owner,
                            "base_full_support_index":support,
                            "strict_entire_branch":result["arithmetic_strict_entire_origin_branch"],
                            "strict_radius_margin":result["strict_radius_margin"]})
            print(json.dumps({"independent_two_origin_actual_whole_branch":len(checked),
                              "leaf":index,"origin_center":owner,
                              "strict":result["arithmetic_strict_entire_origin_branch"]}),flush=True)
        claimed = item["strict_origin_branch_proofs"]
        if (
            len(claimed) != len({proof["origin_center_label"] for proof in claimed})
            or any(proof not in item["all_actual_branch_trials"] for proof in claimed)
            or {proof["origin_center_label"] for proof in claimed} != strict
            or item["both_entire_origin_branches_strict"] != (strict == {16,25})
        ):
            raise ValueError("two-origin strict owner union/target classification changed")
        if strict == {16,25}:
            strict_whole.add(index)
            # These kernel functions, regardless of the target leaf location,
            # must not rule out BOTH origin possibilities of the actual root.
            for proof in claimed:
                key = proof["base_full_support_index"],proof["origin_center_label"],F(proof["origin_multiplier"])
                root_possible.append(root_positive(original,kernels[key]))
            if not any(root_possible):
                raise ValueError("distinct origin kernel union falsely rules out known exact covering root")
    advertised = {item["actual_prior_OPEN_leaf"]["index"]
                  for item in record["new_actual_whole_OPEN_leaves_with_BOTH_strict_branches"]}
    if strict_whole != advertised:
        raise ValueError("independent complete two-origin payment set differs")
    rejected = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid new origin-mode control accepted: "+label)
    changed = deepcopy(record)
    changed["pending_closed_leaf_boxes"].pop()
    reject("unpaid-origin-leaf-omitted",lambda:retention(changed,seed,pending))
    changed = deepcopy(record)
    changed["arithmetic_ledger"].pop(0)
    reject("old580-strict-ledger-row-removed",lambda:retention(changed,seed,pending))
    changed = deepcopy(record)
    changed["full134rod_supports"].pop()
    reject("old-full134-positive-support-truncated",lambda:retention(changed,seed,pending))
    if kernels:
        kernel = next(iter(kernels.values()))
        changed_kernel = {**kernel,"boundary_origin_constant":F(0)}
        if kernel["origin_multiplier"] > 0:
            reject("nonzero-origin-constant-dropped",lambda:energy.kernel_scope(changed_kernel))
        changed_kernel = {**kernel,"radius_squared_budget_weight":kernel["original_physical_rod_weight_sum"]}
        if kernel["origin_multiplier"] > 0:
            reject("virtual-mu-budget-dropped",lambda:energy.kernel_scope(changed_kernel))
        changed_kernel = {**kernel,"distinct_full134rod_60free_positive_candidate_kernel":True}
        reject("new-origin-mode-forged-as-old-full134",lambda:energy.kernel_scope(changed_kernel))
    targets = record["new_actual_whole_OPEN_leaves_with_BOTH_strict_branches"]
    if targets:
        changed = deepcopy(record)
        changed["new_actual_whole_OPEN_leaves_with_BOTH_strict_branches"][0]["strict_origin_branch_proofs"].pop()
        reject("one-origin-branch-forged-as-whole-leaf",lambda:retention(changed,seed,pending))
        changed = deepcopy(record)
        changed["new_actual_whole_OPEN_leaves_with_BOTH_strict_branches"].append(deepcopy(targets[0]))
        reject("two-origin-whole-leaf-paid-twice",lambda:retention(changed,seed,pending))
        changed = deepcopy(record)
        leaf = changed["new_actual_whole_OPEN_leaves_with_BOTH_strict_branches"][0]["actual_prior_OPEN_leaf"]
        leaf["lower"][0] = str((F(leaf["lower"][0])+F(leaf["upper"][0]))/2)
        reject("proper-origin-subbox-relabelled-as-whole",lambda:retention(changed,seed,pending))
        changed = deepcopy(record)
        proof = changed["new_actual_whole_OPEN_leaves_with_BOTH_strict_branches"][0]["strict_origin_branch_proofs"][0]
        proof["arithmetic_result"]["strict_energy_margin"] = "0"
        reject("zero-origin-branch-margin-promoted",lambda:retention(changed,seed,pending))
    for text,digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("two-origin source changed during independent whole-domain arithmetic")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("two-origin diagnosis changed during independent whole-domain arithmetic")
    inventory.update(record["input_sha256"])
    inventory.update({
        linux(args.diagnosis):args.diagnosis_sha256,linux(__file__):binding.sha(__file__),
        linux(domains.__file__):binding.sha(domains.__file__),
        linux(independent_kernel.__file__):binding.sha(independent_kernel.__file__),
    })
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,"actual_source_closed_box":row,
        "source_file_sha256":seed["source_file_sha256"],"diagnosis_sha256":args.diagnosis_sha256,
        "actual_checked920_predecessor_sha256":source.SEED_SHA,
        "actual_checked920_predecessor_controls_sha256":source.CONTROL_SHA,
        "actual_independent_origin_kernel_square_completion_controls":identities,
        "actual_independently_recomputed_whole_origin_branch_bounds":checked,
        "independent_sine_square_secant_and_positive_quadratic_point_controls":3*len(checked),
        "all_actual_complete_two_branch_leaf_payments_independently_reconstructed":sorted(strict_whole),
        "new_strict_whole_old_OPEN_leaf_count":len(strict_whole),"remaining_OPEN_leaf_count":len(remaining),
        "all_old2999_closed_domains_shared_boundaries_AND580_strict_rows_retained":list(retained),
        "known_exact_root_not_excluded_by_any_new_complete_two_origin_kernel_union":True,
        "actual_origin_constant_budget_mode_branch_subset_and_retention_rejections":rejected,
        "old_mathematics_qualified_REUSE_NOT_fresh_all_old_leaf_replay":True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "independent_complete_two_origin_whole_leaf_controls_completed_NOT_admission":True,
        "new_complete_two_branch_whole_leaves":len(strict_whole),"remaining_OPEN":len(remaining),
        "actual_branch_bounds_independently_recomputed":len(checked),
        "actual_rejection_controls":len(rejected),"global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
