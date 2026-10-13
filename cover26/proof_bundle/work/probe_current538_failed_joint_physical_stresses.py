"""NEW joint references/positive stresses for actual checked failed whole domains.

Old failures are source/ranking DATA only. Fresh exact physical-only bounds,
not numeric minima or extra-origin initialization, decide whole exclusions.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_reuse_source as source
import probe_latest918_joint_origin_stress_batch as joint
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current538-failed-whole-leaf-joint-fresh-physical-stresses-v1"
OLD = Path("outputs/n26-current750-physical-support-reuse256-diagnostic-v1.json")
OLD_CONTROL = Path("outputs/n26-current750-physical-support-reuse256-independent-controls-v1.json")
OLD_SHA = "2960609b6de9ff58541e237222e5caa0afb74c3b5b1e4f2645c77b173d99ac7f"
OLD_CONTROL_SHA = "b59e3549b47f19badfabd5fd730e939b9820c432726c15d6e53055329bdeeacd"
PROOF = Path("work/n26-current538-failed-joint-physical-stresses-proof.md")


def inputs(args):
    original,model,seed,control,row,pending,supports,kernels,references,arcs,inventory = source.inputs(args)
    if args.expected_open != 538 or binding.sha(OLD) != OLD_SHA or binding.sha(OLD_CONTROL) != OLD_CONTROL_SHA:
        raise ValueError("failed-joint continuation changed actual538 or checked failed44 pair")
    prior,prior_controls = binding.read(OLD),binding.read(OLD_CONTROL)
    failed = prior["actual_failed_whole_leaf_indices"]
    if (
        prior_controls["diagnosis_sha256"] != OLD_SHA
        or prior_controls["actual_failed_whole_leaf_indices"] != failed
        or seed["retained_failed_CURRENT_whole_leaf_indices"] != failed or len(failed) != 44
        or seed["actual_complete_physical_reuse_batch_sha256"] != OLD_SHA
        or seed["actual_complete_physical_reuse_controls_sha256"] != OLD_CONTROL_SHA
        or prior_controls["all_actual_new_whole_physical_bounds_including_failures_independently_recomputed"] is None
    ):
        raise ValueError("failed-joint continuation lost its actual independent failed44 ancestry")
    current = {leaf["index"]:leaf for leaf in pending}
    attempts = {item["actual_current_whole_OPEN_leaf"]["index"]:item for item in prior["actual_current_whole_leaf_trials"]}
    ranked = []
    for index in failed:
        old = attempts[index]
        if (
            current.get(index) != old["actual_current_whole_OPEN_leaf"]
            or old["strict_whole_physical_leaf"] is not False
            or old["selected_strict_physical_proof"] is not None
        ):
            raise ValueError("old failed domain no longer equals an actual current538 whole OPEN")
        usable = [trial for trial in old["actual_physical_support_trials"] if trial["arithmetic_result"] is not None]
        if not usable:
            raise ValueError("failed-joint priority requires an actual recorded exact old bound")
        best = max(usable,key=lambda trial:F(trial["arithmetic_result"]["strict_radius_margin"]))
        ranked.append((F(best["arithmetic_result"]["strict_radius_margin"]),index,best["full_support_index"]))
    ranked.sort(reverse=True)
    inventory.update({
        linux(OLD):OLD_SHA,linux(OLD_CONTROL):OLD_CONTROL_SHA,linux(__file__):binding.sha(__file__),
        linux(joint.__file__):binding.sha(joint.__file__),linux(joint.fresh.__file__):binding.sha(joint.fresh.__file__),
        linux(PROOF):binding.sha(PROOF),
    })
    return original,model,seed,control,row,pending,supports,kernels,ranked,arcs,inventory


def ownership(record,seed,pending):
    actual = {leaf["index"]:leaf for leaf in pending}
    failed = set(seed["retained_failed_CURRENT_whole_leaf_indices"])
    seen,strict = set(),set()
    for item in record["actual_failed_whole_leaf_fresh_trials"]:
        leaf = item["actual_current_failed_whole_OPEN_leaf"]
        index = leaf["index"]
        if index in seen or index not in failed or actual.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"}:
            raise ValueError("fresh joint target duplicated, clipped, paid or not actually failed")
        seen.add(index)
        proofs = []
        for trial in item["fresh_physical_trials"]:
            result = trial["arithmetic_result"]
            proved = result is not None and result["arithmetic_strict_target_test_passed"] is True
            if trial["strict_entire_physical_leaf"] != proved:
                raise ValueError("fresh joint target promoted a numeric/failed physical proposal")
            if proved:
                if (
                    trial["certificate"] is None or trial["certificate"]["schema"] != source.earlier.suggestion.exact.SCHEMA
                    or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
                ):
                    raise ValueError("fresh joint target lacks an exact entire physical bound")
                proofs.append(trial)
        chosen = item["selected_strict_physical_proof"]
        if item["strict_whole_physical_leaf"] != bool(proofs) or (chosen is not None) != bool(proofs) or chosen is not None and chosen not in proofs:
            raise ValueError("fresh joint whole-target strict subset differs")
        if proofs:
            strict.add(index)
    if (
        record["new_strict_whole_leaf_indices"] != sorted(strict)
        or record["prospective_remaining_OPEN_after_independent_join"] != 538-len(strict)
        or record["all962_old_strict_rows19supports_and_old_histories_UNMODIFIED"] is not True
    ):
        raise ValueError("fresh joint failure continuation count or retained history differs")
    return strict


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=8)
    parser.add_argument("--parts",type=int,default=32)
    parser.add_argument("--iterations",type=int,default=900)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 44 or not 1 <= args.parts <= 64 or not 1 <= args.iterations <= 1500:
        raise ValueError("fresh bounded failed-joint physical experiment required")
    original,model,seed,controls,row,pending,supports,kernels,ranked,arcs,inventory = inputs(args)
    by_index = {leaf["index"]:leaf for leaf in pending}
    results,strict = [],[]
    print(json.dumps({"actual_checked_failed44_and_current538_reconstructed":True,
                      "new_joint_weight_targets":[index for score,index,support in ranked[:args.limit]],
                      "old_bounds_NOT_repeated_no_old_paid_leaves_used":True}),flush=True)
    for number,(old_score,index,support) in enumerate(ranked[:args.limit],1):
        leaf,attempts,chosen = by_index[index],[],None
        for owner in (16,25):
            turns,free_points,primal = joint.joint_suggestion(
                original,model,kernels[support],leaf,owner,args.iterations)
            weights,mu,fit = joint.stress_suggestion(model,turns,free_points,owner)
            kernel_certificate,base = joint.fresh.exact_base(model,weights)
            certificate,result,suggestions = source.earlier.suggestion.suggest(
                base,original["matrix"],list(map(F,leaf["lower"])),list(map(F,leaf["upper"])),
                turns,original["radius"],arcs,args.parts)
            proved = result is not None and result["arithmetic_strict_target_test_passed"] is True
            trial = {
                "origin_owner_for_numerical_initialization_ONLY":owner,
                "fresh_physical_kernel_certificate":kernel_certificate,
                "joint_reference_turns":list(map(str,turns)),"joint_rational60_free_points":free_points,
                "certificate":certificate,"arithmetic_result":result,"strict_entire_physical_leaf":proved,
                "numerical_joint_reference_NOT_proof":primal,"numerical_stress_fit_NOT_proof":fit,
                "numeric_virtual_mu_NOT_used_in_physical_bound":float(mu),
                "numerical_curvature_suggestions_NOT_proof":suggestions,
            }
            attempts.append(trial)
            print(json.dumps({"actual_failed_whole_leaf":index,"new_joint_initializer_owner":owner,
                              "fresh_exact_entire_PHYSICAL_leaf_strict":proved,
                              "exact_energy_margin_display":float(F(result["strict_energy_margin"])) if result else None,
                              "no_actual_origin_owner_requirement_no_virtual_budget":True}),flush=True)
            if proved:
                chosen = trial
                strict.append(index)
                break
        results.append({"actual_current_failed_whole_OPEN_leaf":leaf,"fresh_physical_trials":attempts,
                        "selected_strict_physical_proof":chosen,"strict_whole_physical_leaf":chosen is not None})
        print(json.dumps({"new_joint_failed_leaf_attempts":number,"of":args.limit,
                          "new_strict_old_FAILED_whole_leaves":len(strict),"current538_UNMODIFIED":True}),flush=True)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("fresh failed-joint original input changed during exact calculations")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_checked_prior_failed_diagnosis_sha256":OLD_SHA,"actual_checked_prior_failed_controls_sha256":OLD_CONTROL_SHA,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "actual_failed_whole_leaf_fresh_trials":results,"new_strict_whole_leaf_indices":sorted(strict),
        "prospective_remaining_OPEN_after_independent_join":538-len(strict),
        "all962_old_strict_rows19supports_and_old_histories_UNMODIFIED":True,
        "all15_anchor_angles60_free_positions_jointly_varied_without_symmetry":True,
        "numerical_origin_constraint_USED_ONLY_to_suggest_new_PHYSICAL_weights":True,
        "all_NEW_physical_kernel_inverses_and_whole_bounds_freshly_computed_NO_origin_budget":True,
        "new_independent_fresh_inverse_arithmetic_and_failed_source_controls_STILL_required":True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    ownership(report,seed,pending)
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"fresh_failed_joint_physical_primary_completed_NOT_admission":True,
                      "new_strict_old_FAILED_whole_leaves":len(strict),
                      "prospective_remaining_OPEN_PENDING_independent_join":538-len(strict)}),flush=True)


if __name__ == "__main__":
    main()
