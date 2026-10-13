"""Independent complete byte and source-root accounting check after forests."""

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
    digest = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "overlay", "overlay-replay", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    initial = sha(args.current_audit)
    current = read(args.current_audit)
    if (not current["current_bound_bytes_rechecked"]
            or not current["candidate_forest_actual_published_replay_matched_and_semantics_replayed_here"]
            or current["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or current["full_catalog_complete"] is not False or current["global_optimality_proved"] is not False):
        raise ValueError("candidate forest current scope or pending global obligations changed")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("duplicate normalized candidate forest current paths")
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("candidate forest current bound bytes changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({"current_digests_rechecked": number, "total": len(inventory)}), flush=True)
    accepted = read(args.overlay / "VERIFIED.json")
    if (read(args.overlay_replay) != accepted or accepted["verified"] is not True
            or accepted["unresolved_closed_angle_boxes"] != current["candidate_angle_unresolved_closed_boxes"]
            or accepted["new_whole_candidate_source_roots_lower_bounded"]
            != current["candidate_forest_new_whole_source_roots_lower_bounded"]):
        raise ValueError("candidate forest actual acceptance, replay and current counts disagree")
    incoming = read(args.overlay / "SOURCE-PENDING-ANGLES.json")
    certificate = read(args.overlay / "CERTIFICATE.json")
    indices = certificate["discharged_actual_source_root_indices"]
    payments = read(args.overlay / "ROOT-PAYMENTS.json")
    remaining = read(args.overlay / "PENDING-ANGLES.json")
    if (len(set(indices)) != len(indices)
            or [row["source_OPEN_index"] for row in payments] != indices
            or [row for row in incoming if row["index"] not in indices] != remaining
            or any(not row["source_candidate_root_fully_lower_bounded"] for row in payments)
            or any(row["source_candidate_root_strictly_empty"] and row["counts"]["LOCAL"] for row in payments)
            or len(payments) + len(remaining) != len(incoming)
            or len(incoming) != accepted["source_actual_remaining_candidate_roots"]):
        raise ValueError("candidate forest final accounting lost or falsely emptied a source root")
    for path in (args.overlay / "VERIFIED.json", args.overlay_replay, args.overlay / "PENDING-ANGLES.json"):
        if normalized.get(str(path.resolve())) != sha(path):
            raise ValueError("candidate forest actual current result is not bound")
    frontier_path = local_path(current["current_frontier_actual_file"])
    frontier = read(frontier_path)
    if (normalized.get(str(frontier_path.resolve())) != sha(frontier_path)
            or len(frontier["pending_states"]) != current["Rstar_conditional_frontier_pending_subtrees"]
            or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or sha(args.current_audit) != initial):
        raise ValueError("candidate forest changed global frontier, local allowance or current audit")
    pool = read(args.current_audit.with_name(args.current_audit.stem + "-closed-type-pool.json"))
    receipts = read(args.current_audit.with_name(args.current_audit.stem + "-closed-receipt-checks.json"))
    if (len(pool) != current["joined_closed_full_type_codes_in_these_two_catalogues"]
            or len(receipts) != current[
                "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"]):
        raise ValueError("candidate forest current extension lost historical proof retention")
    report = {"schema": "N26-independent-candidate-forest-current-final-digest-recheck-v1",
              "all_current_file_digests_rehashed": True, "current_file_digests_rechecked": len(inventory),
              "current_audit_sha256": initial,
              "candidate_forest_actual_published_replay_exactly_matches_acceptance": True,
              "new_complete_candidate_source_roots_lower_bounded": len(payments),
              "candidate_angle_unresolved_closed_boxes": len(remaining),
              "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
              "all_incoming_candidate_source_roots_discharged_or_retained_exactly": True,
              "LOCAL_equality_regions_never_declared_empty": True,
              "retained_closed_full_type_codes": len(pool), "retained_checked_proof_receipts": len(receipts),
              "radius_scope": current["radius_scope"], "r_strict_interval": current["r_strict_interval"],
              "full_catalog_complete": False, "global_lower_bound_proved": False,
              "global_optimality_proved": False, "n27_started": False, "executed_checker_sha256": sha(__file__)}
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
