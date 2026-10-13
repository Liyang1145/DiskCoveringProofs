"""Actual latest DATA + synthetic final-shape controls, not geometry/current adoption."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_latest_signed_full134_current_accounting as accounting


def sha(path):
    import hashlib
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024*1024), b""):
            value.update(block)
    return value.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "history-data-bundle", "root25-seed", "root25-diagnosis",
                 "root25-controls", "root28-v8", "root28-grown-diagnosis",
                 "root28-grown-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    paths = {name: getattr(args, name.replace("-", "_")) for name in (
        "root25-seed", "root25-diagnosis", "root25-controls", "root28-v8",
        "root28-grown-diagnosis", "root28-grown-controls")}
    digests = {name: sha(path) for name, path in paths.items()}
    accepted_source = read(args.source / "VERIFIED.json")
    incoming = read(args.source / "PENDING-ANGLES.json")
    history_acceptance = read(args.history_data_bundle / "VERIFIED.json")
    history_manifest = read(args.history_data_bundle / "MANIFEST.json")
    history_path = args.history_data_bundle / "SOURCE-ROOT-HISTORY.json"
    if (sha(args.source / "PENDING-ANGLES.json") != accepted_source["files"]["PENDING-ANGLES.json"]
            or history_manifest["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")
            or history_acceptance["files"]["SOURCE-ROOT-HISTORY.json"] != sha(history_path)
            or read(args.history_data_bundle / "SOURCE-PENDING-ANGLES.json") != incoming):
        raise ValueError("accounting fixture changed actual accepted source/history DATA")
    prior_history = read(history_path)
    records = {25: read(args.root25_diagnosis), 28: read(args.root28_grown_diagnosis)}
    seeds = {25: read(args.root25_seed), 28: read(args.root28_v8)}
    controls25, controls28 = read(args.root25_controls), read(args.root28_grown_controls)
    if (controls25["diagnosis_sha256"] != digests["root25-diagnosis"]
            or controls25["seed_sha256"] != digests["root25-seed"]
            or controls28["diagnosis_sha256"] != digests["root28-grown-diagnosis"]
            or controls28["actual_checked_latest_v8_forest_sha256"] != digests["root28-v8"]
            or controls28["fresh_grown_full134rod_strict_whole_closed_targets_independently_checked"] != 96
            or len(controls28["actual_latest_lineage_grown_region_subset_history_and_payment_guards_rejected"]) != 23):
        raise ValueError("accounting uses wrong latest producer/control lineage,not actual grown-v9")
    by_index = {row["index"]: row for row in incoming}
    prior = {row["source_OPEN_index"]: row for row in prior_history}
    classifications, payments, ledgers = [], [], []
    retained_by_index = dict(prior)
    # Independent construction from ACTUAL records. These final-shaped
    # objects are deliberately in-memory synthetic fixtures,not receipts.
    for index, mode in ((25, "latest-root25-extended-signed"), (28, "latest-root28-grown-full134rod")):
        record, row, seed = records[index], by_index[index], seeds[index]
        closed = len(record["pending_closed_leaf_boxes"]) == 0
        item = {
            "source_OPEN_index": index, "actual_source_closed_box": row, "forest_mode": mode,
            "source_candidate_root_fully_lower_bounded": closed,
            "source_candidate_root_strictly_empty": closed and record["arithmetic_result"]["counts"]["LOCAL"] == 0,
            "fresh_full_source_geometry_result": record["arithmetic_result"],
            "unresolved_closed_leaf_boxes": len(record["pending_closed_leaf_boxes"]),
        }
        classifications.append(item)
        ledgers.append({"source_OPEN_index": index, "exact_closed_leaf_ledger": record["arithmetic_ledger"]})
        if closed:
            payments.append(item)
            retained_by_index.pop(index, None)
        else:
            retained_by_index[index] = {
                "source_OPEN_index": index, "actual_source_closed_box": row, "forest_mode": mode,
                "nodes": record["nodes"], "alternative_supports": record["alternative_supports"],
                "full134rod_supports": record.get("full134rod_supports", []),
                "accepted_source_classification": item, "strict_closed_leaf_ledger": record["arithmetic_ledger"],
                "prior_accepted_history_retained_identically": prior.get(index),
                "actual_latest_arithmetic_baseline_retained_identically": seed,
            }
    paid_indices = {row["source_OPEN_index"] for row in payments}
    remaining = [row for row in incoming if row["index"] not in paid_indices]
    retained = [retained_by_index[index] for index in sorted(retained_by_index)]
    current = {
        "schema": accounting.CURRENT_SCHEMA, "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "original_U_current_pending_subtrees_unchanged": 3922,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "latest_forest_new_whole_source_roots_lower_bounded": len(payments),
        "remaining_latest_partial_root_histories": len(retained),
    }
    accepted_shape = {
        "source_actual_remaining_candidate_roots": len(incoming),
        "new_whole_candidate_source_roots_lower_bounded": len(payments),
        "new_strictly_empty_source_roots": sum(row["source_candidate_root_strictly_empty"] for row in payments),
        "unresolved_closed_angle_boxes": len(remaining),
        "remaining_root_partial_histories_retained": len(retained),
    }
    values = {
        "current": current, "accepted": accepted_shape, "incoming": incoming, "prior_history": prior_history,
        "records": records, "seeds": seeds, "classifications": classifications,
        "payments": payments, "remaining": remaining, "retained": retained, "ledgers": ledgers,
    }
    result = accounting.gate(**values)
    if payments or len(remaining) != len(incoming):
        raise ValueError("actual incomplete latest records were incorrectly represented as whole-root payments")
    rejected = []

    def reject(label, **changed):
        try:
            accounting.gate(**{**values, **changed})
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid latest current accounting accepted: "+label)

    reject("actual-source-whole-root-omitted", remaining=remaining[1:])
    reject("actual-source-whole-root-repeated", remaining=remaining+remaining[:1])
    reject("actual-source-root-order-or-row-substituted", remaining=list(reversed(remaining)))
    reject("latest-grown-history-dropped", retained=[row for row in retained if row["source_OPEN_index"] != 28])
    reject("latest-root25-history-dropped", retained=[row for row in retained if row["source_OPEN_index"] != 25])
    reject("latest-history-repeated", retained=retained+retained[:1])
    reject("proper-grown-targets-paid-as-whole-source-root", payments=[classifications[1]])
    wrong = list(classifications)
    wrong[1] = {**wrong[1], "source_candidate_root_fully_lower_bounded": True}
    reject("retained-OPEN-forest-classified-as-whole-root-closed", classifications=wrong)
    wrong = list(classifications)
    wrong[1] = {**wrong[1], "source_candidate_root_strictly_empty": True}
    reject("retained-OPEN-and-equality-scope-laundered-as-empty", classifications=wrong)
    wrong = list(retained)
    at = next(i for i, row in enumerate(wrong) if row["source_OPEN_index"] == 28)
    wrong[at] = {**wrong[at], "nodes": seeds[28]["nodes"]}
    reject("actual-grown-v9-history-reset-to-v8", retained=wrong)
    wrong = list(retained)
    at = next(i for i, row in enumerate(wrong) if row["source_OPEN_index"] == 25)
    wrong[at] = {**wrong[at], "alternative_supports": records[25]["alternative_supports"][:-1]}
    reject("latest-positive-support-prefix-truncated", retained=wrong)
    wrong = list(retained)
    at = next(i for i, row in enumerate(wrong) if row["source_OPEN_index"] == 28)
    wrong[at] = {**wrong[at], "strict_closed_leaf_ledger": records[28]["arithmetic_ledger"][1:]}
    reject("latest-strict-closed-leaf-ledger-truncated", retained=wrong)
    reject("complete-actual-root28-role-omitted", records={25: records[25]})
    reject("latest-output-closed-ledger-role-omitted", ledgers=ledgers[:1])
    reject("current-remaining-root-count-forged", current={**current, "candidate_angle_unresolved_closed_boxes": 0})
    reject("current-original-LOCAL-enlarged", current={**current, "original_52_coordinate_local_allowance_unchanged": "1"})
    reject("current-unrestricted-or-global-optimality-promoted", current={**current, "global_optimality_proved": True})
    reject("current-false-new-whole-root-count", current={**current, "latest_forest_new_whole_source_roots_lower_bounded": 1})
    reject("acceptance-shape-false-removal-count", accepted={**accepted_shape, "new_whole_candidate_source_roots_lower_bounded": 1})
    reject("acceptance-shape-missing-latest-history-count", accepted={**accepted_shape, "remaining_root_partial_histories_retained": 0})
    bad_owner = {**remaining[0], "index": True}
    reject("boolean-current-whole-root-owner", remaining=[bad_owner, *remaining[1:]])
    module_digest, executed_digest = sha(Path(accounting.__file__)), sha(Path(__file__))
    for name, path in paths.items():
        if sha(path) != digests[name]:
            raise ValueError("actual latest record/control changed during independent accounting guards")
    report = {
        "schema": "N26-independent-latest-signed-full134rod-final-accounting-contract-controls-v1",
        "verified": False, "actual_latest_producer_and_control_sha256": digests,
        "actual_source_acceptance_DATA_sha256": sha(args.source / "VERIFIED.json"),
        "actual_source_pending_DATA_sha256": sha(args.source / "PENDING-ANGLES.json"),
        "actual_prior_accepted_history_DATA_sha256": sha(history_path),
        "synthetic_final_shapes_derived_from_ACTUAL_latest_records": True,
        "synthetic_final_shapes_are_NOT_geometry_acceptance_or_current_adoption": True,
        "actual_grown_v9_NOT_replaced_by_v8_or_old_fixture": True,
        "actual_incomplete_forests_paid_whole_roots": 0,
        "independent_exact_accounting_result": result,
        "actual_invalid_root_history_ledger_count_and_scope_controls_rejected": rejected,
        "ENTIRE_source_model_forest_geometry_and_complete_current_join_NOT_executed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": executed_digest, "tested_pure_final_accounting_sha256": module_digest,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_latest_records_independent_final_accounting_controls_completed": True,
        "actual_rejections": len(rejected), "actual_whole_root_payments": 0,
        "synthetic_shapes_NOT_geometry_or_current_acceptance": True,
    }), flush=True)


if __name__ == "__main__":
    main()
