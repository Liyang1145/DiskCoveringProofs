"""Fresh whole OPEN-leaf energy on actual root25v4, retaining all prior proof.

Reconstructs the original model from actual source inputs, not a typed cache.
Uses existing134-rod correlated arithmetic with NEW width-balanced suggestions.
No old source, node, support, leaf ledger or live frozen executor is edited.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_balanced_correlated_diagonal_suggestion as suggestion
import n26_effective_resistance_local_entry as model_source
import n26_mixed_full134rod_support_forest as mixed
import n26_sharp_radius_constraints as sharp
import verify_conditional_force_stage as binding


CURRENT = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
FINAL = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
SEED = Path("outputs/n26-candidate-root25-preserved-full134rod-regions-forest-diagnosis-v4.json")
CONTROLS = Path("outputs/n26-candidate-root25-preserved-full134rod-regions-independent-controls-v1.json")
CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
SEED_SHA = "4914725c65f3995014a30484f2e4a37428701efe02bbed2edce98f70d96626cc"
CONTROL_SHA = "a9c80ec8bcf6d2d861cbab828e2c3d150d7a230b8a4cef78e5801d651b29a7d0"
SCHEMA = "N26-unaccepted-root25v4-preserved-width-balanced-whole-leaf-energy-v1"


def source_inputs():
    current,final = binding.read(CURRENT),binding.read(FINAL)
    if (
        binding.sha(CURRENT) != CURRENT_SHA or final["current_audit_sha256"] != CURRENT_SHA
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(current["files"])
        or current["global_optimality_proved"] is not False
        or binding.sha(SEED) != SEED_SHA or binding.sha(CONTROLS) != CONTROL_SHA
    ):
        raise ValueError("balanced whole-leaf probe changed actual completed proof-time pair/v4 seed")
    seed,controls = binding.read(SEED),binding.read(CONTROLS)
    if (
        seed["source_OPEN_index"] != 25 or controls["diagnosis_sha256"] != SEED_SHA
        or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
        or controls["retained_OPEN_leaves"] != 984
        or any(item["verified"] is not False or item["new_geometric_payments"] != 0
               for item in (seed,controls))
    ):
        raise ValueError("balanced whole-leaf probe replaced latest root25v4 with old history")
    reference_path = Path("outputs/n26-leaf-pinned-candidate-angles-v2/REFERENCE-PINNING.json")
    cap_path = Path("outputs/n26-current-partial-prefix-energy-v1/CAP-CERTIFICATE.json")
    for path in (reference_path,cap_path):
        if current["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("balanced whole-leaf probe original source model is not bound")
    reference,cap = binding.read(reference_path),binding.read(cap_path)
    data = model_source.base.source_gate(
        Path("outputs/n26-positive-stress-v1"),Path("outputs/n26-centered-local-barrier-v2"),
        Path("outputs/n26-candidate-transport-control-v1"),reference)
    geometry,edges,_,t = model_source.base.root_geometry(*data[:3])
    if reference["edges"] != [list(edge) for edge in edges] or F(
            data[4]["unrestricted_center_neighbourhood_halfwidth_before_rotation"]) != F(7,800000):
        raise ValueError("fresh balanced original rod/rotation/LOCAL source changed")
    radius,arcs = F(current["r_strict_interval"][1]),model_source.base.arcs
    if radius*radius < t[1]:
        raise ValueError("actual same-root radius upper does not contain its original root")
    caps,_ = sharp.cap_gate(radius,cap,arcs)
    terminal = data[3]["states"][-1]
    spec = {"N":26,"B":16,"next":26,"faces":terminal["faces"]}
    matrix,_ = sharp.constraint_matrix(spec,caps)
    original = {"data":tuple(data[:5]),"reference":reference,"cap":cap,"matrix":matrix,"radius":radius}
    model = mixed.model_gate(original)
    kernels = mixed.full_support_gate(model,seed["full134rod_supports"])
    owner = Path("outputs/n26-current-candidate-owned-forest-v8")
    accepted = binding.read(owner/"VERIFIED.json")
    selected = [CURRENT,FINAL,SEED,CONTROLS,reference_path,cap_path,owner/"VERIFIED.json",*data[5]]
    for name,digest in seed["source_file_sha256"].items():
        path = owner/name
        if binding.sha(path) != digest or accepted["files"][name] != digest:
            raise ValueError("actual v4 source root/history owner changed")
        selected.append(path)
    row = next(row for row in binding.read(owner/"PENDING-ANGLES.json") if row["index"] == 25)
    if row != seed["actual_source_closed_box"]:
        raise ValueError("actual balanced source root bounds clipped/changed")
    leaves = mixed.partition(matrix,row,seed["nodes"],mixed.old.prior.prior.tighten,False)
    independent = mixed.partition(matrix,row,seed["nodes"],mixed.old.prior.prior.independently_contract,True)
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    if leaves != independent or pending != seed["pending_closed_leaf_boxes"]:
        raise ValueError("fresh original model did not reconstruct actual v4 whole closed partition")
    modules = (
        suggestion,suggestion.exact,suggestion.exact.full,suggestion.exact.full.hull,
        suggestion.exact.full.hull.quadratic,mixed,model_source,model_source.original_pin,
        model_source.base,model_source.base.iv,model_source.base.geo,sharp,
    )
    selected.extend(Path(module.__file__) for module in modules)
    selected.extend((Path(arcs.__file__),Path(__file__)))
    inventory = {linux(path):binding.sha(path) for path in selected}
    return original,model,kernels,seed,controls,row,pending,arcs,inventory


def rank_leaves(original,kernels,pending):
    root = original["matrix"]
    # Numerical ranking ONLY: all corners of broad coordinates and a midpoint.
    # This is not a lower bound; exact closed-domain calculations follow.
    root_row = binding.read(SEED)["actual_source_closed_box"]
    broad = [i for i,(a,b) in enumerate(zip(root_row["sharp_lower"],root_row["sharp_upper"]))
             if F(b)-F(a) > F(1,10**7)]
    if len(broad) > 10:
        raise ValueError("whole-leaf ranking refuses unbounded corner allocation")
    masks = np.arange(1<<len(broad))
    bit = np.array([((masks>>j)&1) for j in range(len(broad))]).T
    prepared = []
    for kernel in kernels:
        left = np.array([i for i,j,w in kernel["pairs"]])
        right = np.array([j for i,j,w in kernel["pairs"]])
        weights = np.array([float(F(w,kernel["inverse_denominator"]*sum(kernel["weights"])))
                            for i,j,w in kernel["pairs"]])
        prepared.append((left,right,weights))
    scores = []
    for leaf in pending:
        lo,hi = np.array(list(map(float,map(F,leaf["lower"])))),np.array(list(map(float,map(F,leaf["upper"]))))
        points = np.tile((lo+hi)/2,(len(masks),1))
        points[:,broad] = lo[broad]+bit*(hi-lo)[broad]
        points = np.vstack((points,(lo+hi)/2))
        points = np.column_stack((np.zeros(len(points)),points))
        values = []
        for left,right,weights in prepared:
            energy = 2*(1-np.cos(2*np.pi*(points[:,right]-points[:,left])))@weights
            values.append(float(min(energy))-float(original["radius"]**2))
        support = int(np.argmax(values))
        scores.append({"actual_OPEN_leaf_index":leaf["index"],
                       "sampled_corner_score_NOT_a_lower_bound":values[support],
                       "suggested_existing_full_support_index":support})
    return sorted(scores,key=lambda row:row["sampled_corner_score_NOT_a_lower_bound"],reverse=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=16)
    parser.add_argument("--parts",type=int,default=8)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 64 or not 1 <= args.parts <= 64:
        raise ValueError("fresh report and bounded actual whole-leaf experiment required")
    original,model,kernels,seed,controls,row,pending,arcs,inventory = source_inputs()
    rankings = rank_leaves(original,kernels,pending)
    by_index = {leaf["index"]:leaf for leaf in pending}
    nodes,ledger = deepcopy(seed["nodes"]),deepcopy(seed["arithmetic_ledger"])
    results,new_strict = [],[]
    print(json.dumps({"actual_root25v4_seed_preserved":True,"all984_actual_OPEN_domains_reconstructed":True,
                      "selected_whole_OPEN_leaves":args.limit,
                      "top_sampled_scores_NOT_lower_bounds":rankings[:3]}),flush=True)
    for number,rank in enumerate(rankings[:args.limit],1):
        leaf = by_index[rank["actual_OPEN_leaf_index"]]
        lower,upper = list(map(F,leaf["lower"])),list(map(F,leaf["upper"]))
        reference = [(a+b)/2 for a,b in zip(lower,upper)]
        suggestion.exact.full.hull.quadratic.reference_gate(reference,lower,upper,original["matrix"])
        support = rank["suggested_existing_full_support_index"]
        certificate,result,numerical = suggestion.suggest(
            kernels[support],original["matrix"],lower,upper,reference,original["radius"],arcs,args.parts)
        trials = [{"reference_strategy":"exact_feasible_whole_leaf_midpoint",
                   "full_support_index":support,"certificate":certificate,
                   "exact_whole_leaf_result":result,"numerical_suggestions_NOT_proofs":numerical}]
        strict = result is not None and result["arithmetic_strict_target_test_passed"] is True
        if strict:
            node = {"kind":mixed.KIND,"full_support_index":support,"certificate":certificate}
            if nodes[leaf["index"]] != {"kind":"OPEN"}:
                raise ValueError("balanced whole-leaf experiment would overwrite an old payment")
            nodes[leaf["index"]] = node
            ledger.append({**leaf,"kind":mixed.KIND,"full_support_index":support,
                           "certificate":certificate,"arithmetic_result":result})
            new_strict.append({"actual_seed_v4_OPEN_leaf":leaf,"full_support_index":support,
                               "certificate":certificate,"arithmetic_result":result})
        results.append({"actual_latest_v4_whole_OPEN_leaf":leaf,"numerical_ranking_NOT_proof":rank,
                        "trials":trials,"fresh_exact_entire_OPEN_leaf_strict":strict})
        print(json.dumps({"actual_whole_leaf_attempt":number,"of":args.limit,"leaf":leaf["index"],
                          "strict_entire_old_OPEN_leaf":strict,"total_new_strict":len(new_strict),
                          "exact_energy_margin_display":float(F(result["strict_energy_margin"])) if result else None,
                          "formal_geometric_payments":0}),flush=True)
    ledger.sort(key=lambda row:row["index"])
    remaining = [leaf for leaf in pending if nodes[leaf["index"]] == {"kind":"OPEN"}]
    record = {"nodes":nodes,"alternative_supports":seed["alternative_supports"],
              "full134rod_supports":seed["full134rod_supports"],"arithmetic_ledger":ledger}
    retention = mixed.retention_gate(seed,record)
    if len(remaining)+len(new_strict) != len(pending):
        raise ValueError("whole-leaf continuation lost an unresolved source")
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("balanced whole-leaf actual input changed during calculation")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "actual_seed_v4_sha256":SEED_SHA,"actual_seed_v4_controls_sha256":CONTROL_SHA,
        "actual_proof_time_current_sha256":CURRENT_SHA,
        "fresh_actual_original_model_134rod_inverse_and_all984_OPEN_domains_reconstructed":True,
        "typed_context_or_cached_model_NOT_imported":True,
        "numerical_full984_ranking_NOT_a_lower_bound":rankings,
        "actual_entire_leaf_energy_trials":results,"new_exact_strict_whole_old_OPEN_leaves":new_strict,
        "new_exact_strict_whole_old_OPEN_leaf_count":len(new_strict),
        **record,"pending_closed_leaf_boxes":remaining,
        "immutable_v4_node_support_and_strict_ledger_retention_counts":list(retention),
        "unchanged_old_v4_arithmetic_explicitly_REUSED_NOT_a_fresh_all_old_leaf_replay":True,
        "all_NEW_actual_whole_leaf_energy_bounds_freshly_recomputed":True,
        "no_proper_subbox_claimed_as_whole_old_OPEN_leaf":True,
        "all_other_984_unselected_or_failed_whole_OPEN_leaves_retained":True,
        "remaining_OPEN_leaf_count":len(remaining),
        "independent_new_whole_leaf_arithmetic_AND_old_retention_controls_STILL_required":True,
        "entire_latest_source_model_history_geometry_admission_NOT_performed":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"balanced_whole_leaf_probe_completed_NOT_geometry_admission":True,
                      "new_strict_whole_old_OPEN_leaves":len(new_strict),"remaining_OPEN":len(remaining),
                      "all_v4_history_preserved":True,"global_optimality_proved":False}),flush=True)


if __name__ == "__main__":
    main()
