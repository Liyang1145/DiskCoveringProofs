"""Independent final byte rehash for the accepted partial-energy current chain."""

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
    h = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "overlay", "overlay-replay", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original_hash = sha(args.current_audit)
    current = read(args.current_audit)
    if (not current["current_bound_bytes_rechecked"]
            or not current["current_partial_energy_actual_published_replay_matched_and_semantics_replayed_here"]
            or current["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or current["full_catalog_complete"] is not False or current["global_optimality_proved"] is not False):
        raise ValueError("partial current scope or pending global obligations changed")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("duplicate normalized partial current inventory paths")
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("partial current bound bytes changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({"current_digests_rechecked": number, "total": len(inventory)}), flush=True)
    accepted = read(args.overlay / "VERIFIED.json")
    if (read(args.overlay_replay) != accepted or accepted["verified"] is not True
            or accepted["conditional_frontier_pending_subtrees"] != current["Rstar_conditional_frontier_pending_subtrees"]
            or accepted["new_strict_radius_conditional_whole_partial_subtrees_excluded"]
            != current["new_strict_radius_conditional_partial_energy_whole_subtrees_excluded"]):
        raise ValueError("partial actual acceptance, replay and current totals disagree")
    for path in (args.overlay / "VERIFIED.json", args.overlay_replay, args.overlay / "FRONTIER.json"):
        if normalized.get(str(path.resolve())) != sha(path):
            raise ValueError("partial actual proof or current frontier is not bound")
    pool = read(args.current_audit.with_name(args.current_audit.stem + "-closed-type-pool.json"))
    receipts = read(args.current_audit.with_name(args.current_audit.stem + "-closed-receipt-checks.json"))
    if (len(pool) != current["joined_closed_full_type_codes_in_these_two_catalogues"]
            or len(receipts) != current[
                "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"]
            or sha(args.current_audit) != original_hash):
        raise ValueError("partial historical proof retention or final audit bytes changed")
    report = {"schema": "N26-independent-partial-energy-current-final-digest-recheck-v1",
              "all_current_file_digests_rehashed": True, "current_file_digests_rechecked": len(inventory),
              "current_audit_sha256": original_hash,
              "partial_actual_published_replay_exactly_matches_acceptance": True,
              "Rstar_conditional_frontier_pending_subtrees": current["Rstar_conditional_frontier_pending_subtrees"],
              "strict_partial_whole_subtrees_excluded": accepted[
                  "new_strict_radius_conditional_whole_partial_subtrees_excluded"],
              "retained_closed_full_type_codes": len(pool), "retained_checked_proof_receipts": len(receipts),
              "candidate_angle_unresolved_closed_boxes": current["candidate_angle_unresolved_closed_boxes"],
              "radius_scope": current["radius_scope"], "r_strict_interval": current["r_strict_interval"],
              "full_catalog_complete": False, "global_lower_bound_proved": False,
              "global_optimality_proved": False, "n27_started": False, "executed_checker_sha256": sha(__file__)}
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
