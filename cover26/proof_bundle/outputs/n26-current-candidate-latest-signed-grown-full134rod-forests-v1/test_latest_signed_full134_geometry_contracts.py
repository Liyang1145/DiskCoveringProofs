"""Actual root25/v8 ownership-retention guards, NOT grown-v9 geometry acceptance.

Root28 v8 is used only to test baseline retention and to verify that its older
role is REJECTED for grown-v9 production. No v9 report is fabricated.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import verify_conditional_force_stage as binding
import verify_latest_candidate_signed_full134rod_forests as checker


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "root25-seed", "root25-diagnosis", "root25-controls",
                 "root28-v8", "root28-v8-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    input_digests = {name: binding.sha(getattr(args, name.replace("-", "_"))) for name in
                    ("root25-seed", "root25-diagnosis", "root25-controls",
                     "root28-v8", "root28-v8-controls")}
    seed = binding.read(args.root25_seed)
    latest25, controls25 = binding.read(args.root25_diagnosis), binding.read(args.root25_controls)
    baseline28, controls28 = binding.read(args.root28_v8), binding.read(args.root28_v8_controls)
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    accepted = binding.read(args.source / "VERIFIED.json")
    if (binding.sha(args.source / "PENDING-ANGLES.json") != accepted["files"]["PENDING-ANGLES.json"]
            or latest25["old_arithmetic_forest_sha256"] != input_digests["root25-seed"]
            or controls25["diagnosis_sha256"] != input_digests["root25-diagnosis"]
            or controls28["diagnosis_sha256"] != input_digests["root28-v8"]
            or len(controls25["actual_rejection_controls_passed"]) != 20
            or len(controls28["actual_rejection_controls_passed"]) != 20):
        raise ValueError("geometry contract tests changed actual completed baseline lineage")
    checker.required_role_gate(25, latest25, controls25)
    retained25 = checker.retention(seed, latest25)
    retained28 = checker.retention(baseline28, baseline28)
    if retained25 != (
            controls25["old_nodes_retained"], controls25["old_positive_supports_retained"],
            controls25["old_proved_closed_leaves_retained"]):
        raise ValueError("new geometry interface reset actual independently checked root25 lineage")
    records = {25: latest25, 28: baseline28}
    checker.root_gate(incoming, records)
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid latest geometry contract accepted: "+label)

    # These use REAL completed objects, not a forged successful grown record.
    reject("actual-v8-baseline-laundered-as-actual-grown-v9",
           lambda: checker.required_role_gate(28, baseline28, controls28))
    reject("generic-root28-controls-substituted-for-root25-specific-controls",
           lambda: checker.required_role_gate(25, latest25, controls28))
    reject("historical-baseline-present-n27-true-not-ignored", lambda:
           checker.unpaid_scope({**seed, "n27_started": True}, legacy_seed=True))
    reject("unknown-baseline-schema-laundered-through-missing-n27", lambda:
           checker.unpaid_scope({**seed, "schema": "UNKNOWN-OLD-SEED"}, legacy_seed=True))
    missing_latest_status = dict(latest25)
    missing_latest_status.pop("n27_started")
    reject("latest-producer-status-omitted-as-if-it-were-historical", lambda:
           checker.unpaid_scope(missing_latest_status))
    for index, old, record in ((25, seed, latest25), (28, baseline28, baseline28)):
        for field, value in (
            ("verified", True), ("new_geometric_payments", 1),
            ("candidate_whole_roots_removed", 1), ("global_lower_bound_proved", True),
            ("global_optimality_proved", True), ("n27_started", True),
        ):
            reject(str(index)+"-unpaid-scope-"+field,
                   lambda field=field, value=value, record=record:
                   checker.unpaid_scope({**record, field: value}))
        bad = {**record, "source_OPEN_index": True}
        reject(str(index)+"-boolean-source-owner",
               lambda bad=bad, old=old: checker.retention(old, bad))
        bad = {**record, "alternative_supports": record["alternative_supports"][1:]}
        reject(str(index)+"-actual-support-prefix-reset",
               lambda bad=bad, old=old: checker.retention(old, bad))
        old_index = old["arithmetic_ledger"][0]["index"]
        bad = {**record, "arithmetic_ledger": [
            leaf for leaf in record["arithmetic_ledger"] if leaf["index"] != old_index]}
        reject(str(index)+"-actual-old-strict-ledger-reset",
               lambda bad=bad, old=old: checker.retention(old, bad))
        nonopen = next(number for number, node in enumerate(old["nodes"]) if node["kind"] != "OPEN")
        nodes = list(record["nodes"])
        nodes[nonopen] = {"kind": "OPEN"}
        bad = {**record, "nodes": nodes}
        reject(str(index)+"-actual-old-nonOPEN-node-reset",
               lambda bad=bad, old=old: checker.retention(old, bad))
        row = deepcopy(record["actual_source_closed_box"])
        row["sharp_lower"][0] = "-100"
        bad = {**record, "actual_source_closed_box": row}
        reject(str(index)+"-whole-current-source-domain-changed",
               lambda bad=bad, old=old: checker.retention(old, bad))
    reject("root28-omitted-for-an-easier-root25-only-interface",
           lambda: checker.root_gate(incoming, {25: latest25}))
    reject("root25-omitted-for-an-easier-root28-only-interface",
           lambda: checker.root_gate(incoming, {28: baseline28}))
    bad = {25: latest25, 28: {**baseline28, "source_OPEN_index": 1794}}
    reject("previously-paid-original-LOCAL-root-reopened",
           lambda: checker.root_gate(incoming, bad))
    duplicated = incoming+incoming[:1]
    reject("duplicate-current-whole-root-in-source",
           lambda: checker.root_gate(duplicated, records))
    if any("n26_typed_arithmetic_context" == name for name in checker.sys.modules):
        raise ValueError("geometry contracts unexpectedly imported a typed source cache")
    for name, digest in input_digests.items():
        if binding.sha(getattr(args, name.replace("-", "_"))) != digest:
            raise ValueError("actual input changed during geometry ownership/retention controls")
    report = {
        "schema": "N26-independent-latest-signed-full134rod-ownership-retention-role-contracts-v1",
        "verified": False,
        "actual_root25_v2_to_v3_retention_counts_checked": list(retained25),
        "actual_root28_v8_baseline_self_retention_mechanism_checked": list(retained28),
        "actual_v8_was_REJECTED_as_grown_v9_NOT_used_to_replace_it": True,
        "actual_ownership_unpaid_scope_retention_and_producer_role_guards_rejected": rejected,
        "actual_input_sha256": input_digests,
        "actual_source_acceptance_sha256": binding.sha(args.source / "VERIFIED.json"),
        "actual_source_pending_sha256": binding.sha(args.source / "PENDING-ANGLES.json"),
        "transitive_local_geometry_imports_checked": len(checker.executed_modules()),
        "typed_arithmetic_context_and_diagnostic_producers_NOT_imported": True,
        "actual_grown_v9_and_its_automatic_controls_NOT_replaced_by_this_baseline_test": True,
        "ENTIRE_source_model_history_and_latest_forest_geometry_acceptance_NOT_executed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_own_full_geometry_executor_sha256": binding.sha(checker.__file__),
        "tested_complete_source_backend_sha256": binding.sha(checker.source_backend.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_latest_geometry_ownership_retention_role_controls_completed": True,
        "actual_rejections": len(rejected), "actual_grown_v9_geometry_NOT_executed": True,
        "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
