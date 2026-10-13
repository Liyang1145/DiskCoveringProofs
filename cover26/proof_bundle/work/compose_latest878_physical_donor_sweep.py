"""Checked arithmetic join: append legitimate PHYSICAL supports, retain origins."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest878_physical_donor_source as source
import test_latest878_physical_donor_sweep as tester
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest-root25-checked-physical134-donor-sweep-composition-v1"
BATCH = Path("outputs/n26-latest878-physical-donor-whole-leaf-sweep-diagnostic-v1.json")
CONTROLS = Path("outputs/n26-latest878-physical-donor-whole-leaf-sweep-independent-controls-v1.json")
mixed = source.ancestor.ancestor.original_source.mixed


def inputs(batch_sha, controls_sha):
    if (
        binding.sha(source.SEED) != source.SEED_SHA or binding.sha(source.CONTROLS) != source.CONTROL_SHA
        or binding.sha(BATCH) != batch_sha or binding.sha(CONTROLS) != controls_sha
    ):
        raise ValueError("physical-only arithmetic join changed actual paired878 or completed batch pair")
    seed, old_controls = binding.read(source.SEED), binding.read(source.CONTROLS)
    batch, controls = binding.read(BATCH), binding.read(CONTROLS)
    source.scope(seed, old_controls)
    supports = batch["actual_fresh_physical_only_supports"]
    if len(supports) != 16:
        raise ValueError("physical-only arithmetic join lost a bound donor")
    for index, support in enumerate(supports):
        if (
            set(support) != {"mode", "kernel_certificate", "suggestion_point_turns"}
            or support["mode"] != mixed.SUPPORT_MODE
            or support["kernel_certificate"] != seed["fresh_joint_origin_supports"][index]["base_kernel_certificate"]
            or len(support["suggestion_point_turns"]) != 15
        ):
            raise ValueError("physical-only arithmetic join relabelled an origin kernel or unbound physical donor")
    tester.scope(batch, seed, supports)
    strict = source.ownership(batch, seed, seed["pending_closed_leaf_boxes"])
    checkpoint_inventory = tester.checkpoint_gate(batch)
    if (
        controls["schema"] != tester.SCHEMA or controls["diagnosis_sha256"] != batch_sha
        or controls["actual_paired878_diagnosis_sha256"] != source.SEED_SHA
        or controls["actual_paired878_controls_sha256"] != source.CONTROL_SHA
        or controls["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or controls["source_file_sha256"] != seed["source_file_sha256"]
        or controls["new_strict_whole_leaf_indices"] != sorted(strict)
        or controls["prospective_arithmetic_remaining_OPEN_after_independent_join"] != 878-len(strict)
        or controls["all2999_closed_domains622_old_strict_rows_and106old_exclusions_retained"] is not True
        or controls["all_old_supports_and_complete_origin_branch_ANDforest_histories_retained"] is not True
        or controls["all16_physical_donor_inverse_identities_freshly_checked"] is not True
        or controls["known_exact_covering_root_not_excluded_by_any_used_physical_kernel"] is not True
        or controls["no_origin_owner_or_virtual_mu_used_in_new_physical_mode"] is not True
        or controls["actual_immutable_whole_attempt_checkpoints_rechecked"] != len(checkpoint_inventory)
        or controls["executed_test_sha256"] != binding.sha(tester.__file__)
        or controls["verified"] is not False or controls["new_geometric_payments"] != 0
        or any(controls[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("physical-only arithmetic join lacks its actual complete independent physical-mode controls")
    checked = {(item["whole_leaf_index"], item["physical_donor_index"]): item
               for item in controls["all_actual_new_whole_physical_bounds_including_failures_independently_recomputed"]}
    for target in batch["actual_physical_only_whole_leaf_trials"]:
        index = target["actual_latest878_whole_OPEN_leaf"]["index"]
        if index not in strict:
            continue
        proof = target["selected_strict_physical_proof"]
        actual = checked[index, proof["physical_donor_index"]]
        if actual["strict_entire_physical_leaf"] is not True or F(actual["strict_radius_margin"]) <= 0:
            raise ValueError("physical-only arithmetic join adopted an unchecked/nonstrict donor proof")
    inventory = {}
    for report in (seed, old_controls, batch, controls):
        for text, digest in report["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("physical-only arithmetic join prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("physical-only arithmetic join prerequisite digest conflict")
            inventory[text] = digest
    inventory.update(checkpoint_inventory)
    inventory.update({
        linux(source.SEED): source.SEED_SHA, linux(source.CONTROLS): source.CONTROL_SHA,
        linux(BATCH): batch_sha, linux(CONTROLS): controls_sha, linux(__file__): binding.sha(__file__),
    })
    return seed, batch, controls, strict, inventory


def compose(seed, batch, strict):
    nodes, ledger = list(seed["nodes"]), list(seed["arithmetic_ledger"])
    offset = len(seed["full134rod_supports"])
    supports = [*seed["full134rod_supports"], *batch["actual_fresh_physical_only_supports"]]
    if len(supports) > mixed.MAX_FULL_SUPPORTS:
        raise ValueError("physical-only arithmetic join exceeds the real full134 support dispatcher limit")
    for target in batch["actual_physical_only_whole_leaf_trials"]:
        leaf, proof = target["actual_latest878_whole_OPEN_leaf"], target["selected_strict_physical_proof"]
        index = leaf["index"]
        if index not in strict:
            continue
        support = offset+proof["physical_donor_index"]
        node = {"kind": mixed.KIND, "full_support_index": support, "certificate": proof["certificate"]}
        nodes[index] = node
        ledger.append({
            **leaf, "kind": mixed.KIND, "full_support_index": support,
            "certificate": proof["certificate"], "arithmetic_result": proof["arithmetic_result"],
        })
    ledger.sort(key=lambda item: item["index"])
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    return nodes, ledger, pending, supports


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--batch-sha256", required=True)
    parser.add_argument("--controls-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve physical-only arithmetic successor")
    seed, batch, controls, strict, inventory = inputs(args.batch_sha256, args.controls_sha256)
    if not strict:
        raise ValueError("zero newly proved entire regions cannot advance arithmetic history")
    nodes, ledger, pending, supports = compose(seed, batch, strict)
    record = {
        "nodes": nodes, "alternative_supports": seed["alternative_supports"],
        "full134rod_supports": supports, "arithmetic_ledger": ledger,
    }
    retained = mixed.retention_gate(seed, record)
    if len(nodes) != 2999 or len(ledger) != 622+len(strict) or len(pending) != 878-len(strict):
        raise ValueError("physical-only arithmetic join lost a whole domain or prior strict row")
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("physical-only arithmetic source changed during composition")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_source_closed_box": seed["actual_source_closed_box"], "source_file_sha256": seed["source_file_sha256"],
        "actual_checked878_predecessor_sha256": source.SEED_SHA,
        "actual_checked878_controls_sha256": source.CONTROL_SHA,
        "actual_complete_physical_sweep_diagnosis_sha256": args.batch_sha256,
        "actual_complete_physical_sweep_controls_sha256": args.controls_sha256,
        "new_whole_actual878_OPEN_leaf_indices": sorted(strict),
        **record, "fresh_joint_origin_supports": seed["fresh_joint_origin_supports"],
        "pending_closed_leaf_boxes": pending, "remaining_OPEN_leaf_count": len(pending),
        "total_whole_original_v4_OPEN_leaves_excluded": 106+len(strict),
        "retained2999_old_nodes92_supports_and622_prior_strict_rows": list(retained),
        "new16_physical_only_supports_appended_after_unchanged_full134_prefix": True,
        "all106_old_exclusions_ANDentire_origin_branch_forest_histories_retained": True,
        "no_old_origin_certificate_or_virtual_budget_relabelled_as_physical": True,
        "old_ANDnew_mathematics_explicit_qualified_checked_REUSE_NOT_full_replay": True,
        "this_is_only_arithmetic_history_composition_NOT_geometry_cache": True,
        "new_independent_global_arithmetic_retention_controls_STILL_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_producer_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "physical_only_checked_arithmetic_join_completed_NOT_admission": True,
        "new_whole_leaf_exclusions": len(strict), "remaining_OPEN": len(pending),
        "old622_rows_and_entire_origin_history_retained": True,
        "actual_physical_full134_support_table_length": len(supports),
    }), flush=True)


if __name__ == "__main__":
    main()
