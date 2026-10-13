"""CURRENT checked arithmetic join, reusing the exact19 support table."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_physical_reuse_source as source
import test_current_physical_support_reuse as tester
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current-root25-physical-support-reuse-composition-v1"


def arguments(parser):
    source.arguments(parser)
    parser.add_argument("--batch",type=Path,required=True)
    parser.add_argument("--batch-sha256",required=True)
    parser.add_argument("--batch-controls",type=Path,required=True)
    parser.add_argument("--batch-controls-sha256",required=True)


def inputs(args):
    seed,old_controls,inventory = source.paired(args)
    if binding.sha(args.batch) != args.batch_sha256 or binding.sha(args.batch_controls) != args.batch_controls_sha256:
        raise ValueError("CURRENT physical join requires actual completed batch/control pair")
    batch,controls = binding.read(args.batch),binding.read(args.batch_controls)
    tester.scope(batch,args,seed)
    strict = source.ownership(batch,seed,seed["pending_closed_leaf_boxes"])
    checkpoints = tester.checkpoint_gate(batch)
    if (
        controls["schema"] != tester.SCHEMA or controls["diagnosis_sha256"] != args.batch_sha256
        or controls["actual_current_seed_file"] != linux(args.seed)
        or controls["actual_current_seed_sha256"] != args.seed_sha256
        or controls["actual_current_controls_file"] != linux(args.seed_controls)
        or controls["actual_current_controls_sha256"] != args.seed_controls_sha256
        or controls["actual_current_OPEN_count"] != args.expected_open
        or controls["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or controls["source_file_sha256"] != seed["source_file_sha256"]
        or controls["new_strict_whole_leaf_indices"] != sorted(strict)
        or controls["prospective_remaining_OPEN_after_independent_join"] != args.expected_open-len(strict)
        or controls["actual_failed_whole_leaf_indices"] != batch["actual_failed_whole_leaf_indices"]
        or controls["all_old_current_nodes_supports_and_strict_rows_retained"] is not True
        or controls["all19_actual_physical_inverse_identities_freshly_checked"] is not True
        or controls["all_existing19_physical_supports_unchanged_NO_append"] is not True
        or controls["known_exact_covering_root_not_excluded_by_any_used_physical_support"] is not True
        or controls["no_origin_owner_or_virtual_mu_used_in_NEW_physical_proofs"] is not True
        or controls["all_actual_immutable_attempt_checkpoints_rechecked"] != len(checkpoints)
        or controls["executed_test_sha256"] != binding.sha(tester.__file__)
        or controls["verified"] is not False or controls["new_geometric_payments"] != 0
        or any(controls[field] is not False for field in
               ("global_lower_bound_proved","global_optimality_proved","n27_started"))
    ):
        raise ValueError("CURRENT physical join lost actual independent whole-domain/mode/retention scope")
    checked = {(item["whole_leaf_index"],item["full_support_index"]):item
               for item in controls["all_actual_new_whole_physical_bounds_including_failures_independently_recomputed"]}
    for target in batch["actual_current_whole_leaf_trials"]:
        index = target["actual_current_whole_OPEN_leaf"]["index"]
        if index not in strict:
            continue
        proof = target["selected_strict_physical_proof"]
        item = checked[index,proof["full_support_index"]]
        if item["strict_entire_physical_leaf"] is not True or F(item["strict_radius_margin"]) <= 0:
            raise ValueError("CURRENT physical join adopted an unchecked/nonstrict entire proof")
    for record in (batch,controls):
        for text,digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("CURRENT physical join actual prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("CURRENT physical join prerequisite conflict")
            inventory[text] = digest
    inventory.update(checkpoints)
    inventory.update({
        linux(args.batch):args.batch_sha256,linux(args.batch_controls):args.batch_controls_sha256,
        linux(__file__):binding.sha(__file__),
    })
    return seed,batch,controls,strict,inventory


def compose(seed,batch,strict):
    nodes,ledger = list(seed["nodes"]),list(seed["arithmetic_ledger"])
    for target in batch["actual_current_whole_leaf_trials"]:
        leaf,proof = target["actual_current_whole_OPEN_leaf"],target["selected_strict_physical_proof"]
        if leaf["index"] not in strict:
            continue
        nodes[leaf["index"]] = {
            "kind":source.MIXED.KIND,"full_support_index":proof["full_support_index"],
            "certificate":proof["certificate"],
        }
        ledger.append({
            **leaf,"kind":source.MIXED.KIND,"full_support_index":proof["full_support_index"],
            "certificate":proof["certificate"],"arithmetic_result":proof["arithmetic_result"],
        })
    ledger.sort(key=lambda item:item["index"])
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    return nodes,ledger,pending


def main():
    parser = argparse.ArgumentParser()
    arguments(parser)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve completed CURRENT physical reuse composition")
    seed,batch,controls,strict,inventory = inputs(args)
    if not strict:
        raise ValueError("zero newly checked whole exclusions cannot advance CURRENT history")
    nodes,ledger,pending = compose(seed,batch,strict)
    arithmetic = {
        "nodes":nodes,"alternative_supports":seed["alternative_supports"],
        "full134rod_supports":seed["full134rod_supports"],"arithmetic_ledger":ledger,
    }
    retained = source.MIXED.retention_gate(seed,arithmetic)
    if (
        len(nodes) != 2999 or len(ledger) != len(seed["arithmetic_ledger"])+len(strict)
        or len(pending) != args.expected_open-len(strict)
        or arithmetic["full134rod_supports"] != seed["full134rod_supports"]
    ):
        raise ValueError("CURRENT physical join changed original domains/ledger or appended a duplicate support")
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("CURRENT physical join prerequisite changed during composition")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_source_closed_box":seed["actual_source_closed_box"],"source_file_sha256":seed["source_file_sha256"],
        "actual_current_predecessor_file":linux(args.seed),"actual_current_predecessor_sha256":args.seed_sha256,
        "actual_current_predecessor_controls_file":linux(args.seed_controls),
        "actual_current_predecessor_controls_sha256":args.seed_controls_sha256,
        "actual_complete_physical_reuse_batch_file":linux(args.batch),
        "actual_complete_physical_reuse_batch_sha256":args.batch_sha256,
        "actual_complete_physical_reuse_controls_file":linux(args.batch_controls),
        "actual_complete_physical_reuse_controls_sha256":args.batch_controls_sha256,
        "new_whole_actual_current_OPEN_leaf_indices":sorted(strict),
        **arithmetic,"fresh_joint_origin_supports":seed["fresh_joint_origin_supports"],
        "pending_closed_leaf_boxes":pending,"remaining_OPEN_leaf_count":len(pending),
        "total_whole_original_v4_OPEN_leaves_excluded":984-len(pending),
        "retained_old_current_nodes_supports_and_strict_rows":list(retained),
        "all19_physical_supports_reused_unchanged_NOT_appended":True,
        "all_old_origin_branch_forest_fresh_shared_and_physical_histories_retained":True,
        "retained_failed_CURRENT_whole_leaf_indices":batch["actual_failed_whole_leaf_indices"],
        "actual_attempt_method_parameters":batch["method_parameters"],
        "old_ANDnew_mathematics_explicit_qualified_checked_REUSE_NOT_full_replay":True,
        "this_is_only_arithmetic_history_composition_NOT_geometry_cache":True,
        "new_independent_global_arithmetic_retention_controls_STILL_required":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "CURRENT_physical_reuse_arithmetic_join_completed_NOT_admission":True,
        "new_whole_leaf_exclusions":len(strict),"remaining_OPEN":len(pending),
        "old_strict_rows_retained":len(seed["arithmetic_ledger"]),"physical_supports_still":19,
    }),flush=True)


if __name__ == "__main__":
    main()
