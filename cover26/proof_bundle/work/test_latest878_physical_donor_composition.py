"""Independent622-row/history retention and legitimate full134 support append."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import compose_latest878_physical_donor_sweep as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-latest-root25-checked-physical134-donor-sweep-composition-v1"


def retention(record, seed, batch, strict, batch_sha, controls_sha):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_checked878_predecessor_sha256"] != producer.source.SEED_SHA
        or record["actual_checked878_controls_sha256"] != producer.source.CONTROL_SHA
        or record["actual_complete_physical_sweep_diagnosis_sha256"] != batch_sha
        or record["actual_complete_physical_sweep_controls_sha256"] != controls_sha
        or record["new_whole_actual878_OPEN_leaf_indices"] != sorted(strict)
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("independent physical join changed exact source, batch, predecessor or scope")
    if (
        len(record["nodes"]) != 2999 or len(record["nodes"]) != len(seed["nodes"])
        or any(record["nodes"][index] != node for index, node in enumerate(seed["nodes"]) if index not in strict)
        or record["alternative_supports"] != seed["alternative_supports"]
        or record["fresh_joint_origin_supports"] != seed["fresh_joint_origin_supports"]
        or record["full134rod_supports"] != [*seed["full134rod_supports"], *batch["actual_fresh_physical_only_supports"]]
    ):
        raise ValueError("independent physical join reset an old node or support/history prefix")
    expected, offset = {}, len(seed["full134rod_supports"])
    for item in batch["actual_physical_only_whole_leaf_trials"]:
        leaf, proof = item["actual_latest878_whole_OPEN_leaf"], item["selected_strict_physical_proof"]
        index = leaf["index"]
        if index not in strict:
            continue
        if seed["nodes"][index] != {"kind": "OPEN"}:
            raise ValueError("independent physical join re-paid an old completed origin/physical leaf")
        support = offset+proof["physical_donor_index"]
        node = {"kind": producer.mixed.KIND, "full_support_index": support, "certificate": proof["certificate"]}
        if record["nodes"][index] != node:
            raise ValueError("independent physical join changed an entire physical bound or support offset")
        expected[index] = {
            **leaf, "kind": producer.mixed.KIND, "full_support_index": support,
            "certificate": proof["certificate"], "arithmetic_result": proof["arithmetic_result"],
        }
    old_rows = {item["index"]: item for item in seed["arithmetic_ledger"]}
    new_rows = {item["index"]: item for item in record["arithmetic_ledger"]}
    if (
        len(old_rows) != 622 or len(new_rows) != len(record["arithmetic_ledger"])
        or len(new_rows) != 622+len(strict) or set(new_rows)-set(old_rows) != strict
        or any(new_rows.get(index) != item for index, item in old_rows.items())
        or any(new_rows.get(index) != item for index, item in expected.items())
    ):
        raise ValueError("independent physical join lost an old622 row or an entire new physical proof")
    pending = [leaf for leaf in seed["pending_closed_leaf_boxes"] if leaf["index"] not in strict]
    if (
        record["pending_closed_leaf_boxes"] != pending or len(pending) != 878-len(strict)
        or record["remaining_OPEN_leaf_count"] != len(pending)
        or record["total_whole_original_v4_OPEN_leaves_excluded"] != 106+len(strict)
    ):
        raise ValueError("independent physical join omitted an unproved whole remainder")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--batch-sha256", required=True)
    parser.add_argument("--controls-sha256", required=True)
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--diagnosis-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual exact completed physical arithmetic join and new output required")
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
            raise AssertionError("invalid physical arithmetic composition accepted: "+label)

    def gate(changed):
        return retention(changed, seed, batch, strict, args.batch_sha256, args.controls_sha256)

    reject("arithmetic-physical-join-promoted-to-global", lambda: gate({**record, "global_optimality_proved": True}))
    reject("old622-strict-row-lost", lambda: gate({**record, "arithmetic_ledger": record["arithmetic_ledger"][1:]}))
    reject("unpaid878-whole-region-omitted", lambda: gate({**record, "pending_closed_leaf_boxes": record["pending_closed_leaf_boxes"][:-1]}))
    reject("old16-origin-history-table-truncated", lambda: gate({
        **record, "fresh_joint_origin_supports": record["fresh_joint_origin_supports"][:-1]}))
    table = list(record["full134rod_supports"])
    table[0] = table[-1]
    reject("old-physical-support-prefix-replaced", lambda: gate({**record, "full134rod_supports": table}))
    nodes = list(record["nodes"])
    nodes[2641] = {"kind": "OPEN"}
    reject("completed2641-origin-forest-reset", lambda: gate({**record, "nodes": nodes}))
    if strict:
        index = min(strict)
        nodes = list(record["nodes"])
        nodes[index] = {**nodes[index], "full_support_index": nodes[index]["full_support_index"]-1}
        reject("fresh-physical-support-offset-forged", lambda: gate({**record, "nodes": nodes}))
        rows = list(record["arithmetic_ledger"])
        position = next(i for i, row in enumerate(rows) if row["index"] == index)
        target = deepcopy(rows[position])
        target["upper"][0] = target["lower"][0]
        rows[position] = target
        reject("proper-subbox-forged-as-whole878-leaf", lambda: gate({**record, "arithmetic_ledger": rows}))
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("physical arithmetic join prerequisite changed during independent checks")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("physical arithmetic join changed during independent checks")
    inventory.update(record["input_sha256"])
    inventory.update({linux(args.diagnosis): args.diagnosis_sha256, linux(__file__): binding.sha(__file__)})
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "diagnosis_sha256": args.diagnosis_sha256,
        "actual_checked878_predecessor_sha256": producer.source.SEED_SHA,
        "actual_checked878_controls_sha256": producer.source.CONTROL_SHA,
        "actual_complete_physical_sweep_diagnosis_sha256": args.batch_sha256,
        "actual_complete_physical_sweep_controls_sha256": args.controls_sha256,
        "new_whole_actual878_OPEN_leaf_indices": sorted(strict),
        "remaining_OPEN_leaf_count": 878-len(strict),
        "total_whole_original_v4_OPEN_leaves_excluded": 106+len(strict),
        "all2999_closed_domains_old92_supports622_old_rows_and_entire_origin_histories_retained": True,
        "new16_real_physical_supports_appended_after_exact_old_full134_prefix": True,
        "actual_physical_full134_support_table_length": len(record["full134rod_supports"]),
        "all_new_whole_leaf_physical_proofs_bind_correct_support_offset_ANDunchanged_whole_domain": True,
        "arithmetic_only_checked_history_composition_NOT_geometry_cache": True,
        "prior_domain_ANDenergy_mathematics_explicit_qualified_REUSE_NOT_fresh_replay": True,
        "actual_scope_retention_history_support_offset_and_subset_rejection_controls": rejected,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "independent_physical_only_arithmetic_join_completed_NOT_admission": True,
        "new_whole_leaf_exclusions": len(strict), "remaining_OPEN": 878-len(strict),
        "all622old_rows_and_entire_origin_history_retained": True,
        "actual_rejection_controls": len(rejected),
    }), flush=True)


if __name__ == "__main__":
    main()
