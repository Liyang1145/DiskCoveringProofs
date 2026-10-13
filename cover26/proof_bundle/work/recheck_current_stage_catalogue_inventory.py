"""Independently rehash the final current inventory and actual replay reports.

This is a byte-consistency check, not a new geometric proof or an extension of
the accepted radius scope. The existing current audit remains authoritative.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys


def local_path(value):
    text = str(value).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    digest = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "stage", "stage-replay", "catalog", "catalog-replay", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    before = sha(args.current_audit)
    current = read(args.current_audit)
    if (not current["current_bound_bytes_rechecked"]
            or current["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or current["original_U_current_pending_subtrees_unchanged"] != 3922
            or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or current["full_catalog_complete"] is not False
            or current["global_optimality_proved"] is not False):
        raise ValueError("current scope or pending global obligations changed")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("current inventory has duplicate normalized paths")
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("current bound bytes changed: " + text)
        if number % 5000 == 0:
            print(json.dumps({"rehash_checked": number, "total": len(inventory)}), flush=True)
    stage = read(args.stage / "VERIFIED.json")
    catalog = read(args.catalog / "VERIFIED.json")
    for acceptance, folder, replay in ((stage, args.stage, args.stage_replay),
                                       (catalog, args.catalog, args.catalog_replay)):
        if read(replay) != acceptance or acceptance["verified"] is not True:
            raise ValueError("actual published replay differs from its accepted report")
        for path in (folder / "VERIFIED.json", replay):
            if normalized.get(str(path.resolve())) != sha(path):
                raise ValueError("actual current acceptance or replay is not bound")
    if (stage["conditional_frontier_pending_subtrees"]
            != current["Rstar_conditional_frontier_pending_subtrees"]
            or stage["event_counts"] != current["new_stage_event_counts"]
            or catalog["selected_terminal_paths"]
            != current["all_current_unresolved_terminal_paths_reconstructed"]
            or catalog["selected_candidate_type_paths"] != current["current_candidate_type_paths"]
            or stage["r_strict_interval"] != current["r_strict_interval"]):
        raise ValueError("current stage, terminal catalogue or same root disagree")
    pool_path = args.current_audit.with_name(args.current_audit.stem + "-closed-type-pool.json")
    receipts_path = args.current_audit.with_name(args.current_audit.stem + "-closed-receipt-checks.json")
    if (len(read(pool_path)) != current["joined_closed_full_type_codes_in_these_two_catalogues"]
            or len(read(receipts_path)) != current[
                "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"]):
        raise ValueError("current historical pool or receipt totals disagree")
    if sha(args.current_audit) != before:
        raise ValueError("current audit changed while its complete inventory was rehashed")
    report = {
        "schema": "N26-independent-final-current-inventory-rehash-v1",
        "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": len(inventory),
        "current_audit_sha256": before,
        "stage_actual_published_replay_exactly_matches_acceptance": True,
        "catalogue_actual_published_replay_exactly_matches_acceptance": True,
        "Rstar_conditional_frontier_pending_subtrees": current[
            "Rstar_conditional_frontier_pending_subtrees"],
        "new_stage_event_counts": stage["event_counts"],
        "retained_closed_full_type_codes": len(read(pool_path)),
        "retained_checked_proof_receipts": len(read(receipts_path)),
        "candidate_angle_unresolved_closed_boxes": current["candidate_angle_unresolved_closed_boxes"],
        "radius_scope": current["radius_scope"],
        "r_strict_interval": current["r_strict_interval"],
        "full_catalog_complete": False,
        "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "n27_started": False,
        "executed_checker_sha256": sha(__file__),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
