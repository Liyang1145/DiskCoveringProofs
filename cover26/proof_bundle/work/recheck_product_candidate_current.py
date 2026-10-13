"""Independent final inventory and exact root/history accounting for products."""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys


SCHEMA = "N26-complete-current-chain-with-product-Taylor-LOCAL-forests-audit-v1"
ACCEPTANCE = "N26-accepted-current-product-Taylor-LOCAL-forests-v1"
CHECKER = "verify_current_candidate_product_forests.py"


def local_path(text):
    text = str(text).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper()+":"+text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/"+text[0].lower()+text[2:])
    return Path(text)


def sha(path):
    digest = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024*1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def accounting_gate(current, accepted, incoming, payments, remaining, history, retained, indices):
    by_index = {row["index"]: row for row in incoming}
    if (any(type(index) is not int for index in by_index) or len(by_index) != len(incoming)
            or any(type(index) is not int for index in indices)
            or len(set(indices)) != len(indices)
            or any(index not in by_index for index in indices)
            or [row["source_OPEN_index"] for row in payments] != indices
            or any(row["actual_source_closed_box"] != by_index[row["source_OPEN_index"]]
                   for row in payments)
            or [row for row in incoming if row["index"] not in indices] != remaining
            or [row for row in history if row["source_OPEN_index"] not in indices] != retained
            or len({row["source_OPEN_index"] for row in history}) != len(history)
            or any(row["source_OPEN_index"] not in by_index
                   or row["actual_source_closed_box"] != by_index[row["source_OPEN_index"]]
                   for row in history)
            or len(payments)+len(remaining) != len(incoming)
            or len(incoming) != accepted["source_actual_remaining_candidate_roots"]
            or len(payments) != accepted["new_whole_candidate_source_roots_lower_bounded"]
            or len(payments) != current["product_new_whole_source_roots_lower_bounded"]
            or len(remaining) != accepted["unresolved_closed_angle_boxes"]
            or len(remaining) != current["candidate_angle_unresolved_closed_boxes"]
            or len(retained) != current["remaining_latest_partial_root_histories"]
            or len(retained) != accepted["remaining_root_partial_histories_retained"]
            or any(row["source_candidate_root_fully_lower_bounded"] is not True
                   or row["source_candidate_root_strictly_empty"] is not False
                   or row["original_LOCAL_equality_region_preserved"] is not True
                   for row in payments)):
        raise ValueError("product final accounting lost exact source roots/history or emptied LOCAL equality")


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "overlay", "overlay-replay", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    initial, current = sha(args.current_audit), read(args.current_audit)
    if (current["schema"] != SCHEMA or current["current_bound_bytes_rechecked"] is not True
            or current["product_actual_published_replay_matched_and_semantics_replayed_here"] is not True
            or current["all_newest_owned_histories_retained_identically"] is not True
            or current["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or current["original_U_current_pending_subtrees_unchanged"] != 3922
            or current["full_catalog_complete"] is not False
            or current["global_lower_bound_proved"] is not False
            or current["global_optimality_proved"] is not False):
        raise ValueError("product current final admission/scope changed")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("product current inventory has duplicate normalized paths")
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("product current dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"product_final_digests_rechecked": number,
                              "total": len(inventory)}), flush=True)
    accepted = read(args.overlay / "VERIFIED.json")
    semantic_path = local_path(current["product_semantic_replay_file"])
    if (accepted["schema"] != ACCEPTANCE or accepted["verified"] is not True
            or read(args.overlay_replay) != accepted or read(semantic_path) != accepted
            or accepted["executed_checker_file"] != CHECKER
            or accepted["executed_checker_sha256"] != accepted["files"][CHECKER]
            or sha(args.overlay / CHECKER) != accepted["executed_checker_sha256"]
            or len(accepted["negative_controls_rejected"]) != 19
            or accepted["accepted_curvature_modes"] != ["difference-product-Taylor"]
            or F(accepted["radius_upper"]) != F(current["r_strict_interval"][1])
            or current["product_actual_full_semantic_exit_code"] != 0):
        raise ValueError("product actual own acceptance/publication/current semantic replays disagree")
    incoming = read(args.overlay / "SOURCE-PENDING-ANGLES.json")
    payments = read(args.overlay / "ROOT-PAYMENTS.json")
    remaining = read(args.overlay / "PENDING-ANGLES.json")
    history = read(args.overlay / "SOURCE-ROOT-HISTORY.json")
    retained = read(args.overlay / "REMAINING-ROOT-HISTORY.json")
    indices = read(args.overlay / "CERTIFICATE.json")["discharged_actual_source_root_indices"]
    accounting_gate(current, accepted, incoming, payments, remaining, history, retained, indices)
    for path in (
        args.overlay / "VERIFIED.json", args.overlay_replay, semantic_path,
        args.overlay / CHECKER, args.overlay / "PENDING-ANGLES.json",
        args.overlay / "REMAINING-ROOT-HISTORY.json",
    ):
        if normalized.get(str(path.resolve())) != sha(path):
            raise ValueError("product actual current executor/acceptance/replay/history not bound")
    if (local_path(current["actual_current_candidate_acceptance"]).resolve()
            != (args.overlay / "VERIFIED.json").resolve()
            or local_path(current["actual_current_candidate_pending_angles"]).resolve()
            != (args.overlay / "PENDING-ANGLES.json").resolve()):
        raise ValueError("product current pointers do not name the actual new candidate source")
    frontier_path = local_path(current["current_frontier_actual_file"])
    frontier = read(frontier_path)
    if (normalized.get(str(frontier_path.resolve())) != sha(frontier_path)
            or len(frontier["pending_states"]) != current["Rstar_conditional_frontier_pending_subtrees"]
            or frontier["radius_scope"] != current["radius_scope"]
            or F(frontier["radius_upper"]) != F(current["r_strict_interval"][1])
            or current["current_transport_frontier_unchanged_by_product_candidate_forest"] is not True):
        raise ValueError("product candidate current changed exact global transport frontier")
    pool = read(args.current_audit.with_name(args.current_audit.stem+"-closed-type-pool.json"))
    receipts = read(args.current_audit.with_name(args.current_audit.stem+"-closed-receipt-checks.json"))
    if (len(pool) != current["joined_closed_full_type_codes_in_these_two_catalogues"]
            or len(receipts) != current[
                "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"]
            or sha(args.current_audit) != initial):
        raise ValueError("product current historical pool, receipts or own snapshot changed")
    report = {
        "schema": "N26-independent-product-forest-current-final-rehash-v1",
        "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": len(inventory), "current_audit_sha256": initial,
        "product_actual_own_acceptance_publication_and_current_semantic_replays_equal": True,
        "new_complete_candidate_source_roots_lower_bounded": len(payments),
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "all_uncovered_whole_roots_and_latest_partial_histories_retained": True,
        "remaining_latest_partial_root_histories": len(retained),
        "Rstar_conditional_frontier_pending_subtrees": current["Rstar_conditional_frontier_pending_subtrees"],
        "retained_closed_full_type_codes": len(pool), "retained_checked_proof_receipts": len(receipts),
        "radius_scope": current["radius_scope"], "r_strict_interval": current["r_strict_interval"],
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_checker_sha256": sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
