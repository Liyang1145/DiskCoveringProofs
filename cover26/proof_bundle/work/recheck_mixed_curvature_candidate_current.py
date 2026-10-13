"""Independent final byte/root/history accounting for new mixed current reports."""

import argparse
import hashlib
import json
from pathlib import Path
import sys


def local_path(text):
    text = str(text).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    value = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def accounting_gate(current, accepted, incoming, payments, remaining,
                    history, retained, indices):
    if (any(type(index) is not int for index in indices)
            or len(set(indices)) != len(indices)
            or [row["source_OPEN_index"] for row in payments] != indices
            or [row for row in incoming if row["index"] not in indices] != remaining
            or [row for row in history if row["source_OPEN_index"] not in indices] != retained
            or len(payments) + len(remaining) != len(incoming)
            or len(incoming) != accepted["source_actual_remaining_candidate_roots"]
            or len(payments) != accepted["new_whole_candidate_source_roots_lower_bounded"]
            or len(payments) != current["mixed_curvature_new_whole_source_roots_lower_bounded"]
            or len(remaining) != current["candidate_angle_unresolved_closed_boxes"]
            or len(retained) != current["remaining_latest_partial_root_histories"]
            or len(retained) != accepted["remaining_root_partial_histories_retained"]
            or len(remaining) != accepted["unresolved_closed_angle_boxes"]
            or any(not row["source_candidate_root_fully_lower_bounded"]
                   or row["source_candidate_root_strictly_empty"] for row in payments)):
        raise ValueError("mixed final accounting lost a root/history or falsely emptied LOCAL equality")


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "overlay", "overlay-replay", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    initial = sha(args.current_audit)
    current = read(args.current_audit)
    if (current["schema"] != "N26-complete-current-chain-with-mixed-curvature-root-covers-audit-v1"
            or current["current_bound_bytes_rechecked"] is not True
            or current["mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here"] is not True
            or current["all_newest_owned_histories_retained_identically"] is not True
            or current["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or current["original_U_current_pending_subtrees_unchanged"] != 3922
            or current["full_catalog_complete"] is not False
            or current["global_optimality_proved"] is not False):
        raise ValueError("mixed current final rehash scope/admission changed")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("mixed current has duplicate normalized file paths")
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("mixed current dependency changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({"mixed_final_digests_rechecked": number,
                              "total": len(inventory)}), flush=True)
    accepted = read(args.overlay / "VERIFIED.json")
    semantic_path = local_path(current["mixed_curvature_semantic_replay_file"])
    if (accepted["verified"] is not True
            or read(args.overlay_replay) != accepted or read(semantic_path) != accepted
            or len(accepted["negative_controls_rejected"]) != 29
            or accepted["accepted_curvature_modes"] != ["constant-hull", "integrated-Taylor"]):
        raise ValueError("mixed actual own acceptance/replays/mode controls disagree")
    incoming = read(args.overlay / "SOURCE-PENDING-ANGLES.json")
    payments = read(args.overlay / "ROOT-PAYMENTS.json")
    remaining = read(args.overlay / "PENDING-ANGLES.json")
    history = read(args.overlay / "SOURCE-ROOT-HISTORY.json")
    retained = read(args.overlay / "REMAINING-ROOT-HISTORY.json")
    indices = read(args.overlay / "CERTIFICATE.json")["discharged_actual_source_root_indices"]
    accounting_gate(current, accepted, incoming, payments, remaining, history, retained, indices)
    for path in (
        args.overlay / "VERIFIED.json", args.overlay_replay, semantic_path,
        args.overlay / "PENDING-ANGLES.json", args.overlay / "REMAINING-ROOT-HISTORY.json",
    ):
        if normalized.get(str(path.resolve())) != sha(path):
            raise ValueError("mixed actual current acceptance/replay/history not bound")
    frontier_path = local_path(current["current_frontier_actual_file"])
    if (normalized.get(str(frontier_path.resolve())) != sha(frontier_path)
            or len(read(frontier_path)["pending_states"]) != current["Rstar_conditional_frontier_pending_subtrees"]
            or current["current_transport_frontier_unchanged_by_mixed_candidate_covers"] is not True):
        raise ValueError("mixed candidate current changed the actual transport partition")
    pool = read(args.current_audit.with_name(args.current_audit.stem + "-closed-type-pool.json"))
    receipts = read(args.current_audit.with_name(args.current_audit.stem + "-closed-receipt-checks.json"))
    if (len(pool) != current["joined_closed_full_type_codes_in_these_two_catalogues"]
            or len(receipts) != current[
                "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"]
            or sha(args.current_audit) != initial):
        raise ValueError("mixed current changed historical pool/receipt counts or its own snapshot")
    report = {
        "schema": "N26-independent-mixed-curvature-current-final-rehash-v1",
        "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": len(inventory), "current_audit_sha256": initial,
        "mixed_actual_own_acceptance_publication_and_current_semantic_replays_equal": True,
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
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
