"""Independent old590/support/full-owner retention of the shared arithmetic join."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import compose_latest910_shared_origin_sweep as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-latest-root25-checked-shared-origin-support-sweep-composition-v1"


def retention(record, seed, batch, strict, batch_sha, control_sha):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_checked910_predecessor_sha256"] != producer.source.SEED_SHA
        or record["actual_checked910_controls_sha256"] != producer.source.CONTROL_SHA
        or record["actual_complete_shared_sweep_diagnosis_sha256"] != batch_sha
        or record["actual_complete_shared_sweep_controls_sha256"] != control_sha
        or record["new_whole_actual910_OPEN_leaf_indices"] != sorted(strict)
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("independent shared join changed exact owner/source/predecessor/unpaid scope")
    if (
        len(record["nodes"]) != 2999 or len(record["nodes"]) != len(seed["nodes"])
        or any(record["nodes"][index] != node for index, node in enumerate(seed["nodes"]) if index not in strict)
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["full134rod_supports"] != seed["full134rod_supports"]
        or record["fresh_joint_origin_supports"] != seed["fresh_joint_origin_supports"]
    ):
        raise ValueError("independent shared join reset an old proof, split or support table")
    expected = {}
    for item in batch["actual_shared_fresh_whole_leaf_trials"]:
        leaf, proofs = item["actual_latest910_whole_OPEN_leaf"], item["strict_origin_branch_proofs"]
        index = leaf["index"]
        if index not in strict:
            continue
        if seed["nodes"][index] != {"kind": "OPEN"} or len(proofs) != 2 or {proof["origin_center_label"] for proof in proofs} != {16,25}:
            raise ValueError("independent shared join lost original OPEN ownership or a whole origin owner")
        branches = [{
            "origin_center_label": proof["origin_center_label"],
            "shared_fresh_support_index": proof["shared_fresh_support_index"],
            "certificate": proof["certificate"],
        } for proof in proofs]
        if record["nodes"][index] != {"kind": producer.KIND, "origin_branch_certificates": branches}:
            raise ValueError("independent shared join altered a checked full-domain certificate")
        expected[index] = {
            **leaf, "kind": producer.KIND, "origin_branch_certificates": branches,
            "checked_shared_sweep_diagnosis_sha256": batch_sha,
            "checked_shared_sweep_independent_controls_sha256": control_sha,
        }
    old_rows = {item["index"]: item for item in seed["arithmetic_ledger"]}
    new_rows = {item["index"]: item for item in record["arithmetic_ledger"]}
    if (
        len(old_rows) != 590 or len(new_rows) != len(record["arithmetic_ledger"])
        or len(new_rows) != 590+len(strict) or set(new_rows)-set(old_rows) != strict
        or any(new_rows.get(index) != item for index, item in old_rows.items())
        or any(new_rows.get(index) != item for index, item in expected.items())
    ):
        raise ValueError("independent shared join lost a590-prior row or a new entire-domain proof")
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        record["pending_closed_leaf_boxes"] != pending or len(pending) != 910-len(strict)
        or record["remaining_OPEN_leaf_count"] != len(pending)
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 74+len(strict)
    ):
        raise ValueError("independent shared join omitted an unproved whole original remainder")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--batch-sha256", required=True)
    parser.add_argument("--controls-sha256", required=True)
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--diagnosis-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual exact completed shared arithmetic join and new independent output required")
    seed, batch, controls, strict, inventory = producer.inputs(args.batch_sha256, args.controls_sha256)
    record = binding.read(args.diagnosis)
    retention(record, seed, batch, strict, args.batch_sha256, args.controls_sha256)
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid shared arithmetic join accepted: "+label)

    def gate(changed):
        return retention(changed, seed, batch, strict, args.batch_sha256, args.controls_sha256)

    reject("arithmetic-join-promoted-to-global", lambda: gate({**record, "global_optimality_proved": True}))
    reject("old590-strict-ledger-row-lost", lambda: gate({**record, "arithmetic_ledger": record["arithmetic_ledger"][1:]}))
    reject("unpaid910-whole-leaf-omitted", lambda: gate({**record, "pending_closed_leaf_boxes": record["pending_closed_leaf_boxes"][:-1]}))
    reject("old16-shared-supports-truncated", lambda: gate({**record, "fresh_joint_origin_supports": record["fresh_joint_origin_supports"][:-1]}))
    nodes = list(record["nodes"])
    nodes[1912] = {"kind": "OPEN"}
    reject("prior-eight-leaf-joint-proof-reset", lambda: gate({**record, "nodes": nodes}))
    if strict:
        index = min(strict)
        nodes = list(record["nodes"])
        nodes[index] = {**nodes[index], "origin_branch_certificates": nodes[index]["origin_branch_certificates"][:1]}
        reject("one-shared-origin-owner-counted-as-two", lambda: gate({**record, "nodes": nodes}))
        rows = list(record["arithmetic_ledger"])
        position = next(i for i, row in enumerate(rows) if row["index"] == index)
        target = deepcopy(rows[position])
        target["upper"][0] = target["lower"][0]
        rows[position] = target
        reject("proper-subbox-forged-as-whole910-leaf", lambda: gate({**record, "arithmetic_ledger": rows}))
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("shared arithmetic join checked prerequisite changed during independent checks")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("shared arithmetic join source changed during independent checks")
    inventory.update(record["input_sha256"])
    inventory.update({linux(args.diagnosis): args.diagnosis_sha256, linux(__file__): binding.sha(__file__)})
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "diagnosis_sha256": args.diagnosis_sha256,
        "actual_checked910_predecessor_sha256": producer.source.SEED_SHA,
        "actual_checked910_controls_sha256": producer.source.CONTROL_SHA,
        "actual_complete_shared_sweep_diagnosis_sha256": args.batch_sha256,
        "actual_complete_shared_sweep_controls_sha256": args.controls_sha256,
        "new_whole_actual910_OPEN_leaf_indices": sorted(strict),
        "remaining_OPEN_leaf_count": 910-len(strict),
        "total_whole_original_v4_OPEN_leaves_excluded": 74+len(strict),
        "all2999_actual_domains_splits_old_supports16_fresh_supports_AND590_old_strict_rows_retained": True,
        "complete2539_two_origin_AND2641_origin_forest_ANDprevious8fresh_whole_leaves_retained": True,
        "every_new_whole_leaf_binds_BOTH_checked_owners_and_unchanged_shared_fresh_supports": True,
        "arithmetic_only_checked_history_composition_NOT_geometry_cache": True,
        "prior_domain_ANDenergy_mathematics_explicit_qualified_REUSE_NOT_fresh_replay": True,
        "actual_scope_retention_owner_and_subset_rejection_controls": rejected,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "independent_shared_fresh_arithmetic_join_completed_NOT_admission": True,
        "new_whole_leaf_exclusions": len(strict), "remaining_OPEN": 910-len(strict),
        "all590old_strict_rows_and16shared_supports_retained": True,
        "actual_rejection_controls": len(rejected),
    }), flush=True)


if __name__ == "__main__":
    main()
