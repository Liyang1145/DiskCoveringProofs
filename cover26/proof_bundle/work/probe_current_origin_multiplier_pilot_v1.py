"""Actual CURRENT failed whole domains with NEW explicit positive origin terms.

No count or history join is performed. Both branches,including equality and
overlap,are required. The geometric original26/origin-premise admission still
remains separate from these exact conditional arithmetic experiments.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_context_v2 as source
import n26_current_origin_multiplier_proposals_v1 as proposal
import probe_joint_remaining_origin25_primal as recovery
import test_full134rod_two_origin_kernel as kernel_check
import test_latest_root25_two_origin_whole_leaves as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current-failed-positive-origin-multiplier-whole-pilot-v1"
PROOF = Path("work/n26-current-positive-origin-multiplier-proof-v1.md")


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=4)
    parser.add_argument("--parts",type=int,default=32)
    parser.add_argument("--branch-tries",type=int,default=2)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 8 or not 1 <= args.parts <= 64 or not 1 <= args.branch_tries <= 4:
        raise ValueError("fresh bounded current positive-origin pilot required")
    original,model,seed,controls,row,pending,supports,bases,turns,arcs,inventory = source.inputs(args)
    proposal.scope(original)
    retained = set(seed["retained_failed_CURRENT_whole_leaf_indices"])
    candidates = [leaf for leaf in pending if leaf["index"] in retained]
    if len(candidates) < args.limit:
        raise ValueError("current origin pilot lacks enough actual retained failed whole domains")
    rankings = proposal.rank(original,row,candidates,bases)
    current = {leaf["index"]:leaf for leaf in candidates}
    for module in (proposal,proposal.origin,proposal.energy,recovery,kernel_check,independent):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(__file__):binding.sha(__file__),linux(PROOF):binding.sha(PROOF)})
    results,identities = [],{}
    print(json.dumps({"actual_CURRENT_failed_whole_domains":len(candidates),
                      "selected_positive_origin_whole_domains":args.limit,
                      "both_actual_original_owners_required":[16,25],
                      "no_physical_or_geometry_history_payment":True}),flush=True)
    for ranked in rankings[:args.limit]:
        leaf = current[ranked["actual_current_whole_leaf_index"]]
        trials,proofs = [],[]
        for owner in (16,25):
            for choice in ranked["owner_proposals"][owner][:args.branch_tries]:
                support,mu = choice["base_full_support_index"],F(choice["origin_multiplier"])
                kernel = proposal.origin.kernel_gate(bases[support],original["data"][3],owner,mu)
                key = (support,owner,str(mu))
                if key not in identities:
                    identities[key] = kernel_check.independent_identity(bases[support],kernel)
                ref,ref_data = recovery.exact_turns(original,leaf,turns[support])
                certificate,result,suggestions = proposal.energy.suggest(
                    kernel,original["matrix"],list(map(F,leaf["lower"])),list(map(F,leaf["upper"])),
                    ref,original["radius"],arcs,args.parts)
                if certificate is not None:
                    recomputed = independent.independent_arithmetic(
                        original,kernel,leaf,{"certificate":certificate,"arithmetic_result":result},arcs)
                    if recomputed != result:
                        raise ValueError("current positive-origin pilot exact result disagrees independently")
                elif result is not None:
                    raise ValueError("current positive-origin LDL failure has a forged exact result")
                strict = bool(result is not None and result["arithmetic_strict_entire_origin_branch"] is True)
                if result is not None and (
                    F(result["radius_squared_budget_W_PLUS_mu"]) != F(sum(bases[support]["weights"]),bases[support]["scale"])+mu
                    or F(result["boundary_origin_constant"]) != kernel["boundary_origin_constant"]
                ):
                    raise ValueError("current origin pilot lost actual virtual budget or indispensable constant")
                trial = {
                    "origin_center_label":owner,"base_full_support_index":support,"origin_multiplier":str(mu),
                    "certificate":certificate,"arithmetic_result":result,
                    "strict_entire_origin_branch":strict,"exact_reference_recovery":ref_data,
                    "fresh_whole_bound_recomputed_with_separate_independent_arithmetic":certificate is not None,
                    "numerical_proposal_NOT_proof":choice,"numerical_curvature_suggestions_NOT_proof":suggestions,
                }
                trials.append(trial)
                print(json.dumps({"actual_CURRENT_whole_leaf":leaf["index"],"origin_owner":owner,
                                  "real_physical_base":support,"positive_origin_mu_display":float(mu),
                                  "strict_entire_origin_branch":strict,
                                  "strict_radius_margin_display":float(F(result["strict_radius_margin"])) if result else None}),
                      flush=True)
                if strict:
                    proofs.append(trial)
                    break
        both = {proof["origin_center_label"] for proof in proofs} == {16,25}
        if both:
            kernels = [proposal.origin.kernel_gate(
                bases[proof["base_full_support_index"]],original["data"][3],
                proof["origin_center_label"],proof["origin_multiplier"]) for proof in proofs]
            if not any(independent.root_positive(original,kernel) for kernel in kernels):
                raise ValueError("current positive-origin complete union falsely excludes the known exact root")
        results.append({"actual_current_failed_whole_OPEN_leaf":leaf,"actual_new_origin_branch_trials":trials,
                        "strict_origin_branch_proofs":proofs,"BOTH_whole_origin_branches_strict":both})
        print(json.dumps({"positive_origin_actual_whole_trials":len(results),"of":args.limit,
                          "both_owner_whole_successes":sum(item["BOTH_whole_origin_branches_strict"] for item in results),
                          "current_OPEN_count_UNMODIFIED":args.expected_open}),flush=True)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("current origin pilot source changed during fresh conditional arithmetic")
    record = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_source_closed_box":row,
        "source_file_sha256":seed["source_file_sha256"],"actual_physical_base_table_count":len(bases),
        "actual_positive_origin_whole_domain_pilot_trials":results,
        "actual_fresh_augmented_inverse_and_nonunit_square_completion_controls":[
            {"base_full_support_index":key[0],"origin_center_label":key[1],"origin_multiplier":key[2],"identity":identity}
            for key,identity in identities.items()],
        "only_TRUE_original_cover_origin_branches_NOT_arbitrary_physical_rod_realizations":True,
        "exact_positive_constant_AND_W_PLUS_mu_budget_retained_NO_old_physical_flag_forged":True,
        "positive_origin_multipliers_are_NEW_proposals_NOT_an_unchanged_failed_physical_bound":True,
        "numerical_corners_and_stationary_multiplier_suggestions_NOT_proofs":True,
        "source_geometry_and_qualified_prior_n25_original26_cardinality_admission_STILL_required":True,
        "current_nodes_tables_all_old_rows_and_pending_domains_UNMODIFIED":True,
        "separate_checked_current_batch_and_history_join_STILL_required_before_any_count_change":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(record,indent=2)+"\n")
    print(json.dumps({"current_positive_origin_pilot_complete_NO_count_change":True,
                      "whole_domains":len(results),
                      "both_owner_whole_successes":sum(item["BOTH_whole_origin_branches_strict"] for item in results)}),
          flush=True)


if __name__ == "__main__":
    main()
