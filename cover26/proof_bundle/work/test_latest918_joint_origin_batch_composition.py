"""Independent full-node/support/ledger retention of the checked fresh batch join."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import compose_latest918_joint_origin_stress_batch as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-latest-root25-checked-fresh-joint-origin-batch-composition-v1"


def retention(record, seed, diagnosis, strict, diagnosis_sha, controls_sha):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_checked918_predecessor_sha256"] != producer.source.SEED_SHA
        or record["actual_checked918_controls_sha256"] != producer.source.CONTROL_SHA
        or record["actual_complete_fresh_joint_batch_diagnosis_sha256"] != diagnosis_sha
        or record["actual_complete_fresh_joint_batch_controls_sha256"] != controls_sha
        or record["new_whole_actual918_OPEN_leaf_indices"] != sorted(strict)
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("independent fresh join changed source, scope, exact batch or predecessor")
    old, new = seed["nodes"], record["nodes"]
    if (
        len(new) != len(old) or len(new) != 2999
        or any(new[index] != node for index, node in enumerate(old) if index not in strict)
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["full134rod_supports"] != seed["full134rod_supports"]
    ):
        raise ValueError("independent fresh join reset an old node or old support")
    supports, expected = record["fresh_joint_origin_supports"], {}
    used, next_index = set(), 0
    for item in diagnosis["actual_joint_stress_whole_leaf_trials"]:
        leaf = item["actual_latest918_whole_OPEN_leaf"]
        index = leaf["index"]
        if index not in strict:
            continue
        if old[index] != {"kind": "OPEN"}:
            raise ValueError("independent fresh join re-paid a nonOPEN predecessor leaf")
        branches = []
        for trial in item["actual_origin_branch_trials"]:
            support_index = next_index
            next_index += 1
            used.add(support_index)
            if supports[support_index] != {
                "origin_center_label": trial["origin_center_label"],
                "base_kernel_certificate": trial["fresh_positive134rod_kernel_certificate"],
                "origin_multiplier": trial["fresh_origin_multiplier"],
            }:
                raise ValueError("independent fresh join altered an actual checked fresh kernel")
            branches.append({
                "origin_center_label": trial["origin_center_label"], "fresh_joint_support_index": support_index,
                "certificate": trial["whole_origin_branch_certificate"],
            })
        if len(branches) != 2 or {branch["origin_center_label"] for branch in branches} != {16, 25}:
            raise ValueError("independent fresh join lost one whole necessary origin owner")
        if new[index] != {"kind": producer.KIND, "origin_branch_certificates": branches}:
            raise ValueError("independent fresh join relabelled or clipped a whole checked proof")
        expected[index] = {
            **leaf, "kind": producer.KIND, "origin_branch_certificates": branches,
            "complete_fresh_joint_batch_diagnosis_sha256": diagnosis_sha,
            "complete_fresh_joint_batch_independent_controls_sha256": controls_sha,
        }
    if used != set(range(len(supports))) or len(supports) != 2*len(strict):
        raise ValueError("independent fresh join changed actual fresh support ownership")
    old_rows = {item["index"]: item for item in seed["arithmetic_ledger"]}
    new_rows = {item["index"]: item for item in record["arithmetic_ledger"]}
    if (
        len(old_rows) != 582 or len(new_rows) != len(record["arithmetic_ledger"])
        or len(new_rows) != 582+len(strict) or set(new_rows)-set(old_rows) != strict
        or any(new_rows.get(index) != item for index, item in old_rows.items())
        or any(new_rows.get(index) != item for index, item in expected.items())
    ):
        raise ValueError("independent fresh join lost a prior strict row or a new complete whole-leaf proof")
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        record["pending_closed_leaf_boxes"] != pending
        or record["remaining_OPEN_leaf_count"] != len(pending)
        or len(pending) != 918-len(strict)
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 66+len(strict)
    ):
        raise ValueError("independent fresh join lost a failed/unselected original OPEN remainder")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--batch-sha256", required=True)
    parser.add_argument("--controls-sha256", required=True)
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--diagnosis-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual exact completed fresh arithmetic join and new output required")
    seed, seed_controls, diagnosis, controls, strict, inventory = producer.inputs(args.batch_sha256, args.controls_sha256)
    record = binding.read(args.diagnosis)
    retention(record, seed, diagnosis, strict, args.batch_sha256, args.controls_sha256)
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid fresh arithmetic composition accepted: "+label)

    def gate(changed):
        return retention(changed, seed, diagnosis, strict, args.batch_sha256, args.controls_sha256)

    reject("arithmetic-join-promoted-to-global", lambda: gate({**record, "global_optimality_proved": True}))
    bad = {**record, "pending_closed_leaf_boxes": record["pending_closed_leaf_boxes"][:-1]}
    reject("unpaid-latest-whole-leaf-omitted", lambda: gate(bad))
    bad = {**record, "arithmetic_ledger": record["arithmetic_ledger"][1:]}
    reject("old582-strict-row-omitted", lambda: gate(bad))
    nodes = list(record["nodes"])
    nodes[2641] = {"kind": "OPEN"}
    reject("completed2641-two-origin-forest-reset", lambda: gate({**record, "nodes": nodes}))
    if strict:
        index = min(strict)
        nodes = list(record["nodes"])
        nodes[index] = {**nodes[index], "origin_branch_certificates": nodes[index]["origin_branch_certificates"][:1]}
        reject("single-origin-branch-counted-as-complete", lambda: gate({**record, "nodes": nodes}))
        rows = list(record["arithmetic_ledger"])
        position = next(i for i, row in enumerate(rows) if row["index"] == index)
        target = deepcopy(rows[position])
        target["upper"][0] = target["lower"][0]
        rows[position] = target
        reject("proper-subbox-forged-as-whole-918-leaf", lambda: gate({**record, "arithmetic_ledger": rows}))
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("fresh arithmetic composition prerequisite changed during independent checks")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("fresh arithmetic composition changed during independent checks")
    inventory.update(record["input_sha256"])
    inventory.update({linux(args.diagnosis): args.diagnosis_sha256, linux(__file__): binding.sha(__file__)})
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "diagnosis_sha256": args.diagnosis_sha256,
        "actual_checked918_predecessor_sha256": producer.source.SEED_SHA,
        "actual_checked918_controls_sha256": producer.source.CONTROL_SHA,
        "actual_complete_fresh_joint_batch_diagnosis_sha256": args.batch_sha256,
        "actual_complete_fresh_joint_batch_controls_sha256": args.controls_sha256,
        "new_whole_actual918_OPEN_leaf_indices": sorted(strict),
        "remaining_OPEN_leaf_count": 918-len(strict),
        "total_whole_original_v4_OPEN_leaves_excluded": 66+len(strict),
        "all2999_actual_domains_splits_old_supports_AND582_old_strict_rows_retained": True,
        "complete2539_two_origin_leaf_AND2641_origin_forest_bindings_retained": True,
        "every_new_whole_leaf_binds_BOTH_checked_owners_and_exact_fresh_kernel_supports": True,
        "arithmetic_only_checked_history_composition_NOT_geometry_cache": True,
        "prior_domain_and_energy_mathematics_explicit_qualified_REUSE_NOT_full_replay": True,
        "actual_scope_retention_owner_and_subset_rejection_controls": rejected,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "independent_fresh_joint_arithmetic_join_completed_NOT_admission": True,
        "new_whole_leaf_exclusions": len(strict), "remaining_OPEN": 918-len(strict),
        "all582prior_strict_rows_retained": True, "actual_rejection_controls": len(rejected),
    }), flush=True)


if __name__ == "__main__":
    main()
