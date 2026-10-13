"""Independent exact root/history accounting; NOT a geometry acceptance.

No source dispatcher, geometry checker, arithmetic context or diagnostic
producer is imported. Full model/forest geometry must pass separately.
"""


MODES = {
    25: "latest-root25-extended-signed",
    28: "latest-root28-grown-full134rod",
}
CURRENT_SCHEMA = "N26-complete-current-chain-with-latest-signed-grown-full134rod-forests-audit-v1"


def owners(rows, key):
    if not isinstance(rows, list):
        raise ValueError("latest independent accounting expects an explicit owned row list")
    result = {}
    for row in rows:
        if not isinstance(row, dict) or type(row.get(key)) is not int or row[key] in result:
            raise ValueError("latest independent accounting repeated or forged a root/history owner")
        result[row[key]] = row
    return result


def expected_classification(index, source_row, record):
    result, pending = record["arithmetic_result"], record["pending_closed_leaf_boxes"]
    if (type(record["source_OPEN_index"]) is not int or record["source_OPEN_index"] != index
            or record["actual_source_closed_box"] != source_row
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False
            or record["n27_started"] is not False
            or not isinstance(pending, list)
            or result["retained_OPEN_leaves"] != len(pending)
            or result["arithmetic_entire_root_lower_bound_cover_completed"] is not (not pending)
            or type(result["counts"]["LOCAL"]) is not int or result["counts"]["LOCAL"] < 0):
        raise ValueError("latest independent accounting changed actual records, unpaid scope or OPEN counts")
    pending_by_index = owners(pending, "index")
    if any(row["kind"] != "OPEN" for row in pending_by_index.values()):
        raise ValueError("latest pending ledger is not the actual OPEN frontier")
    strict = not pending and result["counts"]["LOCAL"] == 0
    return {
        "source_OPEN_index": index, "actual_source_closed_box": source_row,
        "forest_mode": MODES[index],
        "source_candidate_root_fully_lower_bounded": not pending,
        "source_candidate_root_strictly_empty": strict,
        "fresh_full_source_geometry_result": result,
        "unresolved_closed_leaf_boxes": len(pending),
    }


def latest_history(index, row, record, seed, classification, prior):
    return {
        "source_OPEN_index": index, "actual_source_closed_box": row,
        "forest_mode": MODES[index], "nodes": record["nodes"],
        "alternative_supports": record["alternative_supports"],
        "full134rod_supports": record.get("full134rod_supports", []),
        "accepted_source_classification": classification,
        "strict_closed_leaf_ledger": record["arithmetic_ledger"],
        "prior_accepted_history_retained_identically": prior,
        "actual_latest_arithmetic_baseline_retained_identically": seed,
    }


def gate(current, accepted, incoming, prior_history, records, seeds,
         classifications, payments, remaining, retained, ledgers):
    incoming_by_index = owners(incoming, "index")
    prior = owners(prior_history, "source_OPEN_index")
    classified = owners(classifications, "source_OPEN_index")
    paid = owners(payments, "source_OPEN_index")
    remaining_by_index = owners(remaining, "index")
    retained_by_index = owners(retained, "source_OPEN_index")
    ledger_by_index = owners(ledgers, "source_OPEN_index")
    if (set(records) != {25, 28} or set(seeds) != {25, 28}
            or set(classified) != {25, 28} or set(ledger_by_index) != {25, 28}
            or not {25, 28} <= set(incoming_by_index)
            or not set(prior) <= set(incoming_by_index)
            or any(row["actual_source_closed_box"] != incoming_by_index[index]
                   for index, row in prior.items())
            or current["schema"] != CURRENT_SCHEMA
            or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or current["original_U_current_pending_subtrees_unchanged"] != 3922
            or current["full_catalog_complete"] is not False
            or current["global_lower_bound_proved"] is not False
            or current["global_optimality_proved"] is not False
            or current["n27_started"] is not False):
        raise ValueError("latest accounting lost complete source/history ownership or changed n26 scope")
    expected_paid, expected_history = {}, dict(prior)
    for index in (25, 28):
        row, record, seed = incoming_by_index[index], records[index], seeds[index]
        expected = expected_classification(index, row, record)
        if classified[index] != expected:
            raise ValueError("latest root classification is not its complete actual pending partition")
        if (ledger_by_index[index] != {
                "source_OPEN_index": index, "exact_closed_leaf_ledger": record["arithmetic_ledger"]}
                or len(owners(record["arithmetic_ledger"], "index")) != len(record["arithmetic_ledger"])
                or seed["source_OPEN_index"] != index or seed["actual_source_closed_box"] != row):
            raise ValueError("latest accounting changed an actual strict ledger or old arithmetic baseline")
        old_ledger = owners(seed["arithmetic_ledger"], "index")
        new_ledger = owners(record["arithmetic_ledger"], "index")
        if (any(new_ledger.get(number) != leaf for number, leaf in old_ledger.items())
                or len(record["nodes"]) < len(seed["nodes"])
                or record["alternative_supports"][:len(seed["alternative_supports"])]
                != seed["alternative_supports"]
                or record.get("full134rod_supports", [])[:len(seed.get("full134rod_supports", []))]
                != seed.get("full134rod_supports", [])
                or any(node["kind"] != "OPEN" and node != record["nodes"][number]
                       for number, node in enumerate(seed["nodes"]))):
            raise ValueError("latest accounting reset a proved node/support prefix/strict baseline ledger")
        if expected["source_candidate_root_fully_lower_bounded"]:
            expected_paid[index] = expected
            expected_history.pop(index, None)
        else:
            expected_history[index] = latest_history(
                index, row, record, seed, expected, prior.get(index))
    indices = set(expected_paid)
    expected_remaining = [row for row in incoming if row["index"] not in indices]
    expected_retained = [expected_history[index] for index in sorted(expected_history)]
    if (payments != [expected_paid[index] for index in (25, 28) if index in expected_paid]
            or remaining != expected_remaining or retained != expected_retained
            or set(paid) != indices or set(remaining_by_index) != set(incoming_by_index)-indices
            or not set(retained_by_index) <= set(remaining_by_index)
            or len(payments)+len(remaining) != len(incoming)
            or accepted["source_actual_remaining_candidate_roots"] != len(incoming)
            or accepted["new_whole_candidate_source_roots_lower_bounded"] != len(payments)
            or accepted["new_strictly_empty_source_roots"]
            != sum(row["source_candidate_root_strictly_empty"] for row in payments)
            or accepted["unresolved_closed_angle_boxes"] != len(remaining)
            or accepted["remaining_root_partial_histories_retained"] != len(retained)
            or current["candidate_angle_unresolved_closed_boxes"] != len(remaining)
            or current["latest_forest_new_whole_source_roots_lower_bounded"] != len(payments)
            or current["remaining_latest_partial_root_histories"] != len(retained)):
        raise ValueError("latest accounting dropped or falsely paid a whole root/newest partial history")
    return {
        "exact_source_root_partition_and_all_latest_histories_checked": True,
        "whole_source_roots": len(incoming), "new_whole_root_lower_bounds": len(payments),
        "remaining_whole_roots": len(remaining),
        "remaining_latest_partial_histories": len(retained),
        "all_actual_old_nonOPEN_nodes_support_prefixes_and_strict_ledgers_retained": True,
        "LOCAL_equality_never_laundered_as_emptiness": True,
        "accounting_is_NOT_entire_source_model_or_forest_geometry_acceptance": True,
        "new_geometric_payments_by_this_accounting_gate": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
