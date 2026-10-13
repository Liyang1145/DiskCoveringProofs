"""Actual failed pilot domains with fresh preserved-diagonal finer bounds."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_context_v2 as source
import probe_expanded_failed_physical_strip_refinement_v1 as prior
import n26_preserved_diagonal_strip_refinement_v1 as numerical
import test_full134rod_correlated_support as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current-failed-physical-preserved-diagonal-finer-strip-pilot-v1"


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--old-pilot",type=Path,required=True)
    parser.add_argument("--old-pilot-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    parser.add_argument("--parts",type=int,default=32)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.old_pilot) != args.old_pilot_sha256:
        raise ValueError("actual completed old parameter pilot and fresh output required")
    old = binding.read(args.old_pilot)
    original,model,seed,controls,row,pending,supports,kernels,references,arcs,inventory = source.inputs(args)
    if (
        old["schema"] != prior.SCHEMA or old["source_OPEN_index"] != 25
        or old["verified"] is not False or old["new_geometric_payments"] != 0
        or old["global_optimality_proved"] is not False
        or old["actual_current_support_count"] != args.expected_supports
        or old["actual_current_seed_sha256"] != args.seed_sha256
        and seed.get("actual_current_predecessor_sha256") != old["actual_current_seed_sha256"]
    ):
        raise ValueError("preserved-diagonal parameter pilot changed actual model,parent,table or unpaid scope")
    for text,digest in old["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("preserved-diagonal prior parameter data changed")
        if text in inventory and inventory[text] != digest:
            raise ValueError("preserved-diagonal current/old model digest conflict")
        inventory[text] = digest
    actual = {leaf["index"]:leaf for leaf in pending}
    results,seen = [],set()
    for item in old["actual_whole_failed_domain_finer_strip_trials"]:
        leaf,support = item["actual_whole_current_failed_OPEN_leaf"],item["actual_physical_support_index"]
        index = leaf["index"]
        if (
            index in seen or actual.get(index) != leaf or seed["nodes"][index] != {"kind":"OPEN"}
            or type(support) is not int or not 0 <= support < len(kernels)
        ):
            raise ValueError("preserved-diagonal target repeated,clipped,paid or has an unbound physical support")
        seen.add(index)
        old_certificate = item["old_certificate_used_as_parameter_data_ONLY"]
        certificate,result,suggestions = numerical.suggest(
            kernels[support],original["matrix"],list(map(F,leaf["lower"])),list(map(F,leaf["upper"])),
            old_certificate,original["radius"],arcs,args.parts)
        if certificate is not None:
            checked = independent.arithmetic_control(
                original,kernels[support],leaf,
                {"NEW_correlated_quadratic_certificate":certificate,
                 "NEW_correlated_exact_closed_leaf_result":result},arcs)
            if checked != result:
                raise ValueError("preserved-diagonal fresh finer result disagrees independently")
        old_result = item["old_failed_result_used_as_comparison_data_ONLY"]
        improvement = (F(result["boundary_full134rod_correlated_energy_lower"])-
                       F(old_result["boundary_full134rod_correlated_energy_lower"])) if result else None
        results.append({
            "actual_whole_current_failed_OPEN_leaf":leaf,"actual_physical_support_index":support,
            "old_diagonal_reference_and_tangent_PARAMETER_DATA":old_certificate,
            "fresh_finer_preserved_diagonal_certificate":certificate,"fresh_finer_result":result,
            "fresh_bound_recomputed_with_separate_independent_arithmetic":certificate is not None,
            "exact_energy_improvement_over_original16strip_parameter_bound":str(improvement) if improvement is not None else None,
            "numerical_suggestions_NOT_proof":suggestions,
        })
        print(json.dumps({
            "actual_failed_whole_leaf":index,"fresh_finer_parts":args.parts,
            "fresh_preserved_diagonal_whole_physical_strict":result["arithmetic_strict_target_test_passed"] if result else False,
            "energy_improvement_display":float(improvement) if improvement is not None else None,
            "new_radius_margin_display":float(F(result["strict_radius_margin"])) if result else None,
            "original_current_nodes_and_counts_UNMODIFIED":True,
        }),flush=True)
    inventory.update({linux(args.old_pilot):args.old_pilot_sha256})
    for module in (numerical,numerical.exact,numerical.numerical,independent,prior):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory[linux(__file__)] = binding.sha(__file__)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("preserved-diagonal source/parameter inputs changed during fresh arithmetic")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "old_pilot_PARAMETER_DATA_sha256":args.old_pilot_sha256,
        "actual_current_OPEN_count":args.expected_open,"actual_current_support_count":args.expected_supports,
        "actual_preserved_diagonal_finer_whole_domain_trials":results,
        "all_old_diagonals_only_parameters_every_new_finer_LDL_and_bound_freshly_checked":True,
        "no_current_count_change_separate_checked_batch_and_history_join_STILL_required":True,
        "same_real_physical_table_NO_append_no_origin_owner_no_virtual_budget":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as output:
        output.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "preserved_diagonal_finer_pilot_complete_NO_current_count_change":True,
        "whole_domains":len(results),"strict_whole_bounds":sum(bool(item["fresh_finer_result"] and
            item["fresh_finer_result"]["arithmetic_strict_target_test_passed"]) for item in results),
    }),flush=True)


if __name__ == "__main__":
    main()
