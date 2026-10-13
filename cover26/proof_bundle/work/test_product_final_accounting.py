"""Synthetic product bookkeeping controls from unchanged actual source DATA."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import recheck_product_candidate_current as final
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    accepted_source = binding.read(args.source / "VERIFIED.json")
    pending_path = args.source / "PENDING-ANGLES.json"
    if binding.sha(pending_path) != accepted_source["files"]["PENDING-ANGLES.json"]:
        raise ValueError("product accounting fixture changed actual source root DATA")
    incoming = binding.read(pending_path)
    incoming_ids = {row["index"] for row in incoming}
    if "REMAINING-ROOT-HISTORY.json" in accepted_source["files"]:
        history_path = args.source / "REMAINING-ROOT-HISTORY.json"
        if binding.sha(history_path) != accepted_source["files"][history_path.name]:
            raise ValueError("product accounting changed actual mixed source newest history DATA")
        history = binding.read(history_path)
    else:
        history_path = args.source / "PROPOSAL.json"
        if binding.sha(history_path) != accepted_source["files"][history_path.name]:
            raise ValueError("product accounting changed actual owned source newest history DATA")
        history = [item for item in binding.read(history_path)["forests"]
                   if item["source_OPEN_index"] in incoming_ids]
    selected = next(row for row in incoming if row["index"] == 29)
    indices = [29]
    payments = [{
        "source_OPEN_index": 29, "actual_source_closed_box": deepcopy(selected),
        "source_candidate_root_fully_lower_bounded": True,
        "source_candidate_root_strictly_empty": False,
        "original_LOCAL_equality_region_preserved": True,
        "synthetic_accounting_label_NOT_a_geometric_payment": True,
    }]
    remaining = [row for row in incoming if row["index"] not in indices]
    retained = [deepcopy(row) for row in history if row["source_OPEN_index"] not in indices]
    retained_ids = [row["source_OPEN_index"] for row in retained]
    if 959 not in retained_ids:
        raise ValueError("product accounting fixture requires actual newest root959 partial history DATA")
    history959_index = retained_ids.index(959)
    current = {
        "product_new_whole_source_roots_lower_bounded": 1,
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "remaining_latest_partial_root_histories": len(retained),
        "synthetic_accounting_fixture_NOT_actual_current": True,
    }
    accepted = {
        "source_actual_remaining_candidate_roots": len(incoming),
        "new_whole_candidate_source_roots_lower_bounded": 1,
        "unresolved_closed_angle_boxes": len(remaining),
        "remaining_root_partial_histories_retained": len(retained),
        "synthetic_accounting_fixture_NOT_actual_acceptance": True,
    }
    bundle = [current, accepted, incoming, payments, remaining, history, retained, indices]
    final.accounting_gate(*bundle)
    negative = []

    def reject(label, mutation):
        bad = deepcopy(bundle)
        mutation(bad)
        try:
            final.accounting_gate(*bad)
        except (ValueError, KeyError, TypeError):
            negative.append(label)
        else:
            raise AssertionError("invalid product final accounting accepted: "+label)

    reject("product-duplicate-paid-root", lambda bad: bad[7].append(29))
    reject("product-boolean-paid-root", lambda bad: bad[7].__setitem__(0, True))
    reject("product-nonexistent-paid-root", lambda bad: bad[7].__setitem__(0, 100000))
    reject("product-whole-root-payment-omitted", lambda bad: bad[3].clear())
    reject("product-paid-root-domain-clipped", lambda bad:
           bad[3][0]["actual_source_closed_box"]["sharp_lower"].__setitem__(0, "0"))
    reject("product-uncovered-source-root-omitted", lambda bad: bad[4].pop())
    reject("product-covered-root-reintroduced", lambda bad:
           bad[4].append(next(row for row in bad[2] if row["index"] == 29)))
    reject("product-LOCAL-equality-region-called-empty", lambda bad:
           bad[3][0].update(source_candidate_root_strictly_empty=True))
    reject("product-original-LOCAL-preservation-flag-omitted", lambda bad:
           bad[3][0].update(original_LOCAL_equality_region_preserved=False))
    reject("product-lower-bound-payment-flag-omitted", lambda bad:
           bad[3][0].update(source_candidate_root_fully_lower_bounded=False))
    reject("product-latest-root959-history-omitted", lambda bad: bad[6].pop(history959_index))
    reject("product-latest-root959-history-reset", lambda bad:
           bad[6][history959_index].update(nodes=[{"kind": "OPEN"}]))
    reject("product-current-remaining-root-count-changed", lambda bad:
           bad[0].update(candidate_angle_unresolved_closed_boxes=len(remaining)+1))
    reject("product-accepted-incoming-count-changed", lambda bad:
           bad[1].update(source_actual_remaining_candidate_roots=len(incoming)+1))
    reject("product-accepted-latest-history-count-changed", lambda bad:
           bad[1].update(remaining_root_partial_histories_retained=len(retained)+1))
    reject("product-duplicate-actual-source-root", lambda bad: bad[2].append(deepcopy(bad[2][0])))
    report = {
        "schema": "N26-synthetic-product-current-final-accounting-regression-v1",
        "synthetic_exact_source_rows_LOCAL_and_latest_history_partition_passed": True,
        "invalid_accounting_controls_rejected": negative,
        "actual_newest_root959_history_DATA_retained_identically": True,
        "source_acceptance_DATA_sha256": binding.sha(args.source / "VERIFIED.json"),
        "source_pending_DATA_sha256": binding.sha(pending_path),
        "synthetic_remaining_count_NOT_formal_current": len(remaining),
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_optimality_proved": False,
        "tested_final_rehash_executor_sha256": binding.sha(final.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"product_final_accounting_regression_completed": True,
                      "synthetic_invalid_controls": len(negative), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
