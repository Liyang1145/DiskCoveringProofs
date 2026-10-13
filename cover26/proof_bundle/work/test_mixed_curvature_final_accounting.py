"""Synthetic accounting controls using unchanged actual source DATA only.

No geometry result, complete current audit or verified acceptance is written.
The numeric 16-root fixture is explicitly NOT an actual current root count.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import recheck_mixed_curvature_candidate_current as final
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "constant-diagnosis", "integral-diagnosis", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    accepted_source = binding.read(args.source / "VERIFIED.json")
    for name in ("PENDING-ANGLES.json", "PROPOSAL.json", "ROOT-CLASSIFICATION.json"):
        if binding.sha(args.source / name) != accepted_source["files"][name]:
            raise ValueError("synthetic mixed accounting changed actual source DATA")
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    ids = []
    for path in (args.constant_diagnosis, args.integral_diagnosis):
        data = binding.read(path)
        if data["verified"] is not False or data["new_geometric_payments"] != 0:
            raise ValueError("synthetic accounting fixture needs explicit unaccepted diagnoses")
        ids.extend(row["source_OPEN_index"] for row in data["roots"]
                   if row["all_arithmetic_cover_obligations_passed"])
    incoming_ids = {row["index"] for row in incoming}
    history = [item for item in binding.read(args.source / "PROPOSAL.json")["forests"]
               if item["source_OPEN_index"] in incoming_ids]
    # These are SYNTHETIC unit labels to test accounting, not geometry claims.
    payments = [{
        "source_OPEN_index": index,
        "source_candidate_root_fully_lower_bounded": True,
        "source_candidate_root_strictly_empty": False,
        "synthetic_accounting_label_NOT_a_geometric_payment": True,
    } for index in ids]
    remaining = [row for row in incoming if row["index"] not in ids]
    retained = [deepcopy(row) for row in history if row["source_OPEN_index"] not in ids]
    current = {
        "mixed_curvature_new_whole_source_roots_lower_bounded": len(ids),
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "remaining_latest_partial_root_histories": len(retained),
        "synthetic_accounting_fixture_NOT_an_actual_current_audit": True,
    }
    accepted = {
        "source_actual_remaining_candidate_roots": len(incoming),
        "new_whole_candidate_source_roots_lower_bounded": len(ids),
        "unresolved_closed_angle_boxes": len(remaining),
        "remaining_root_partial_histories_retained": len(retained),
        "synthetic_accounting_fixture_NOT_an_actual_acceptance": True,
    }
    bundle = [current, accepted, incoming, payments, remaining, history, retained, ids]
    final.accounting_gate(*bundle)
    rejected = []

    def reject(name, mutation):
        bad = deepcopy(bundle)
        mutation(bad)
        try:
            final.accounting_gate(*bad)
        except (ValueError, KeyError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid mixed final accounting accepted: " + name)

    reject("duplicate-discharged-root-index", lambda bad: bad[7].append(bad[7][0]))
    reject("boolean-discharged-root-index", lambda bad: bad[7].__setitem__(0, True))
    reject("missing-whole-root-payment", lambda bad: bad[3].pop())
    reject("uncovered-source-root-omitted", lambda bad: bad[4].pop())
    reject("covered-root-reintroduced-as-remaining", lambda bad: bad[4].append(
        next(row for row in bad[2] if row["index"] == bad[7][0])))
    reject("LOCAL-equality-region-declared-strictly-empty", lambda bad: bad[3][0].update(
        source_candidate_root_strictly_empty=True))
    reject("root-payment-lower-bound-flag-missing", lambda bad: bad[3][0].update(
        source_candidate_root_fully_lower_bounded=False))
    reject("remaining-root959-history-omitted", lambda bad: bad[6].clear())
    reject("remaining-root959-history-reset-to-OPEN", lambda bad: bad[6][0].update(
        nodes=[{"kind": "OPEN"}]))
    reject("current-root-count-changed", lambda bad: bad[0].update(
        candidate_angle_unresolved_closed_boxes=len(remaining) + 1))
    reject("accepted-source-root-count-changed", lambda bad: bad[1].update(
        source_actual_remaining_candidate_roots=len(incoming) + 1))
    reject("accepted-history-count-changed", lambda bad: bad[1].update(
        remaining_root_partial_histories_retained=len(retained) + 1))
    if [row["source_OPEN_index"] for row in retained] != [959]:
        raise AssertionError("test requires actual newest partial forest959 DATA")
    report = {
        "schema": "N26-synthetic-mixed-curvature-final-accounting-regression-v1",
        "synthetic_exact_source_row_and_latest_history_partition_passed": True,
        "invalid_accounting_controls_rejected": rejected,
        "actual_newest_root959_history_DATA_retained_identically": True,
        "synthetic_remaining_count_16_NOT_a_current_geometry_result": True,
        "verified": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0, "global_optimality_proved": False,
        "tested_final_rehash_executor_sha256": binding.sha(final.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
