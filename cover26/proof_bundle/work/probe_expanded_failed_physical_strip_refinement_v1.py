"""Fresh finer-strip experiments on actual failed whole physical domains.

The old failed batch is parameter data only,not an acceptance premise.
No current node,ledger,support,geometry payment or global status is changed.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_context_v2 as source
import probe_expanded_current_physical_support_reuse_v2 as previous
import test_full134rod_correlated_support as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-expanded-current-failed-physical-finer-strip-pilot-v1"


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--prior-batch",type=Path,required=True)
    parser.add_argument("--prior-batch-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--limit",type=int,default=4)
    parser.add_argument("--parts",type=int,default=32)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 8 or not 1 <= args.parts <= 64:
        raise ValueError("fresh bounded whole-domain finer-strip pilot required")
    if binding.sha(args.prior_batch) != args.prior_batch_sha256:
        raise ValueError("actual frozen failed-batch parameter data changed")
    old = binding.read(args.prior_batch)
    original,model,seed,controls,row,pending,supports,kernels,references,arcs,inventory = source.inputs(args)
    if (
        old["schema"] != previous.SCHEMA or old["source_OPEN_index"] != 25
        or old["actual_source_closed_box"] != row or old["source_file_sha256"] != seed["source_file_sha256"]
        or old["actual_current_support_count"] != args.expected_supports
        or old["verified"] is not False or old["new_geometric_payments"] != 0
        or old["global_optimality_proved"] is not False
        or old["method_parameters"]["parts"] >= args.parts
        or old["actual_current_seed_sha256"] != args.seed_sha256
        and seed.get("actual_complete_physical_reuse_batch_sha256") != args.prior_batch_sha256
    ):
        raise ValueError("pilot parameter data has another actual model,parent or unchanged strip count")
    for text,digest in old["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("pilot old physical parameter prerequisite changed")
        if text in inventory and inventory[text] != digest:
            raise ValueError("pilot old/current model digest conflict")
        inventory[text] = digest
    actual = {leaf["index"]:leaf for leaf in pending}
    failed = set(old["actual_failed_whole_leaf_indices"])
    ranked = []
    for target in old["actual_current_whole_leaf_trials"]:
        leaf = target["actual_current_whole_OPEN_leaf"]
        index = leaf["index"]
        if index not in failed:
            continue
        if (
            actual.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"}
            or target["strict_whole_physical_leaf"] is not False
            or target["selected_strict_physical_proof"] is not None
        ):
            raise ValueError("pilot attempted a clipped,paid or incorrectly failed old domain")
        candidates = [trial for trial in target["actual_physical_support_trials"]
                      if trial["certificate"] is not None and trial["arithmetic_result"] is not None]
        if not candidates:
            continue
        best = max(candidates,key=lambda trial:F(trial["arithmetic_result"]["strict_radius_margin"]))
        ranked.append((F(best["arithmetic_result"]["strict_radius_margin"]),index,best))
    if len(ranked) < args.limit:
        raise ValueError("pilot lacks enough actual failed exact-bound parameter data")
    results = []
    for old_margin,index,old_trial in sorted(ranked,key=lambda item:item[0],reverse=True)[:args.limit]:
        leaf,support = actual[index],old_trial["full_support_index"]
        certificate,result,suggestions = source.earlier.suggestion.suggest(
            kernels[support],original["matrix"],list(map(F,leaf["lower"])),list(map(F,leaf["upper"])),
            list(map(F,old_trial["certificate"]["reference_turns"])),original["radius"],arcs,args.parts)
        checked = None
        if certificate is not None:
            checked = independent.arithmetic_control(
                original,kernels[support],leaf,
                {"NEW_correlated_quadratic_certificate":certificate,
                 "NEW_correlated_exact_closed_leaf_result":result},arcs)
            if checked != result:
                raise ValueError("pilot fresh finer-strip exact result disagrees independently")
        improvement = (F(result["boundary_full134rod_correlated_energy_lower"])
                       -F(old_trial["arithmetic_result"]["boundary_full134rod_correlated_energy_lower"])) if result else None
        results.append({
            "actual_whole_current_failed_OPEN_leaf":leaf,"actual_physical_support_index":support,
            "old_certificate_used_as_parameter_data_ONLY":old_trial["certificate"],
            "old_failed_result_used_as_comparison_data_ONLY":old_trial["arithmetic_result"],
            "fresh_finer_strip_certificate":certificate,"fresh_finer_strip_result":result,
            "fresh_bound_independently_recomputed_with_separate_arithmetic":checked is not None,
            "exact_lower_energy_improvement_over_old_parameter_bound":str(improvement) if improvement is not None else None,
            "numerical_suggestions_NOT_proof":suggestions,
        })
        print(json.dumps({
            "actual_failed_whole_leaf":index,"old_parts":old["method_parameters"]["parts"],"new_parts":args.parts,
            "fresh_whole_physical_strict":result["arithmetic_strict_target_test_passed"] if result else False,
            "lower_energy_improvement_display":float(improvement) if improvement is not None else None,
            "old_radius_margin_display":float(old_margin),
            "new_radius_margin_display":float(F(result["strict_radius_margin"])) if result else None,
            "no_current_or_geometry_payment":True,
        }),flush=True)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("pilot source/model/parameter data changed during fresh arithmetic")
    if binding.sha(args.prior_batch) != args.prior_batch_sha256:
        raise ValueError("pilot old parameter batch changed")
    inventory.update({
        linux(args.prior_batch):args.prior_batch_sha256,linux(__file__):binding.sha(__file__),
        linux(independent.__file__):binding.sha(independent.__file__),
    })
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "prior_failed_batch_PARAMETER_DATA_sha256":args.prior_batch_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_current_support_count":args.expected_supports,
        "old_parts":old["method_parameters"]["parts"],"new_parts":args.parts,
        "actual_whole_failed_domain_finer_strip_trials":results,
        "old_failures_NOT_an_acceptance_premise":True,
        "same_physical_table_NO_append_no_origin_condition_no_virtual_mu":True,
        "current_nodes_ledgers_supports_and_pending_domains_UNMODIFIED":True,
        "separate_checked_batch_and_history_join_required_before_any_count_change":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"actual_failed_finer_strip_pilot_completed_NO_count_change":True,
                      "actual_whole_trials":len(results),
                      "new_strict_whole_bounds":sum(bool(trial["fresh_finer_strip_result"] and
                          trial["fresh_finer_strip_result"]["arithmetic_strict_target_test_passed"]) for trial in results)}),
          flush=True)


if __name__ == "__main__":
    main()
