"""Independent complete inventory/root/history recheck for latest forest current."""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

import n26_latest_signed_full134_current_accounting as accounting


ACCEPTANCE_SCHEMA = "N26-accepted-latest-signed-grown-full134rod-partial-forests-v1"
CHECKER = "verify_latest_candidate_signed_full134rod_forests.py"


def local_path(text):
    text = str(text).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper()+":"+text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/"+text[0].lower()+text[2:])
    return Path(text)


def sha(path):
    value = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024*1024), b""):
            value.update(block)
    return value.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def acceptance_gate(current, accepted, replay, semantic, checker_digest):
    if (current["schema"] != accounting.CURRENT_SCHEMA
            or current["current_bound_bytes_rechecked"] is not True
            or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
            or current["latest_forest_actual_published_replay_matched_and_semantics_replayed_here"] is not True
            or current["latest_forest_source_is_actual_latest_candidate_layer"] is not True
            or current["all_newest_owned_histories_retained_identically"] is not True
            or current["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or current["global_lower_bound_proved"] is not False
            or current["global_optimality_proved"] is not False
            or current["full_catalog_complete"] is not False
            or current["latest_forest_actual_full_semantic_exit_code"] != 0
            or accepted["schema"] != ACCEPTANCE_SCHEMA or accepted["verified"] is not True
            or accepted["radius_scope"] != "same-root-Rstar"
            or F(accepted["radius_upper"]) != F(current["r_strict_interval"][1])
            or accepted != replay or accepted != semantic
            or accepted["executed_checker_file"] != CHECKER
            or accepted["executed_checker_sha256"] != checker_digest
            or accepted["files"][CHECKER] != checker_digest
            or accepted["accepted_forest_modes"] != [
                "latest-root25-extended-signed", "latest-root28-grown-full134rod"]
            or len(accepted["negative_controls_rejected"]) != 21
            or accepted["actual_full_source_replay"][
                "ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here"] is not True
            or accepted["actual_latest_root25_v3_and_root28_grown_v9_replayed_not_reset"] is not True
            or accepted["actual_old_baselines_and_every_strict_ledger_freshly_reconstructed"] is not True
            or accepted["source_identity_and_arithmetic_controls_NOT_used_as_geometry_substitutes"] is not True
            or accepted["LOCAL_equality_feasible_regions_never_declared_empty"] is not True
            or accepted["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or accepted["global_lower_bound_proved"] is not False
            or accepted["global_optimality_proved"] is not False
            or accepted["full_catalog_complete"] is not False
            or accepted["n27_started"] is not False):
        raise ValueError("latest current final lacks actual whole geometry/publication/semantic replay")


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "overlay", "overlay-replay", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    executed_digest, accounting_digest = sha(__file__), sha(accounting.__file__)
    initial = sha(args.current_audit)
    current = read(args.current_audit)
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): value for text, value in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("latest current inventory contains duplicate normalized source paths")
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("latest complete-current dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"latest_forest_final_digests_rechecked": number,
                              "total": len(inventory)}), flush=True)
    accepted = read(args.overlay / "VERIFIED.json")
    semantic_path = local_path(current["latest_forest_semantic_replay_file"])
    checker_path = args.overlay / CHECKER
    acceptance_gate(current, accepted, read(args.overlay_replay), read(semantic_path), sha(checker_path))
    records = {25: read(args.overlay / "ROOT25-DIAGNOSIS.json"),
               28: read(args.overlay / "ROOT28-GROWN-DIAGNOSIS.json")}
    seeds = {25: read(args.overlay / "ROOT25-SEED.json"), 28: read(args.overlay / "ROOT28-V8.json")}
    result = accounting.gate(
        current, accepted, read(args.overlay / "SOURCE-PENDING-ANGLES.json"),
        read(args.overlay / "SOURCE-ROOT-HISTORY.json"), records, seeds,
        read(args.overlay / "ROOT-CLASSIFICATION.json"), read(args.overlay / "ROOT-PAYMENTS.json"),
        read(args.overlay / "PENDING-ANGLES.json"), read(args.overlay / "REMAINING-ROOT-HISTORY.json"),
        read(args.overlay / "LOWER-LEDGER.json"))
    for key, path in (
        ("actual_current_candidate_acceptance", args.overlay / "VERIFIED.json"),
        ("actual_current_candidate_pending_angles", args.overlay / "PENDING-ANGLES.json"),
        ("actual_current_candidate_remaining_history", args.overlay / "REMAINING-ROOT-HISTORY.json"),
    ):
        if (local_path(current[key]).resolve() != path.resolve()
                or normalized.get(str(path.resolve())) != sha(path)):
            raise ValueError("latest final current points to a different actual candidate/history layer")
    for path in (args.overlay_replay, semantic_path, checker_path, Path(__file__), Path(accounting.__file__)):
        if normalized.get(str(path.resolve())) != sha(path):
            raise ValueError("latest final lacks bound actual publication/executor/independent accounting")
    for name in (
        "MANIFEST.json", "VERIFIED.json", "SOURCE-PENDING-ANGLES.json", "SOURCE-ROOT-HISTORY.json",
        "ROOT25-DIAGNOSIS.json", "ROOT25-SEED.json", "ROOT28-GROWN-DIAGNOSIS.json", "ROOT28-V8.json",
        "ROOT-CLASSIFICATION.json", "ROOT-PAYMENTS.json", "PENDING-ANGLES.json",
        "REMAINING-ROOT-HISTORY.json", "LOWER-LEDGER.json",
    ):
        path = args.overlay / name
        if normalized.get(str(path.resolve())) != sha(path):
            raise ValueError("a latest root/history/ledger input changed after its initial full inventory scan")
    frontier_path = local_path(current["current_frontier_actual_file"])
    frontier = read(frontier_path)
    if (normalized.get(str(frontier_path.resolve())) != sha(frontier_path)
            or len(frontier["pending_states"]) != current["Rstar_conditional_frontier_pending_subtrees"]
            or frontier["radius_scope"] != current["radius_scope"]
            or F(frontier["radius_upper"]) != F(current["r_strict_interval"][1])
            or current["current_transport_frontier_unchanged_by_latest_partial_forests"] is not True):
        raise ValueError("latest final lost or changed the actual complete transport frontier")
    pool_path = args.current_audit.with_name(args.current_audit.stem+"-closed-type-pool.json")
    receipts_path = args.current_audit.with_name(args.current_audit.stem+"-closed-receipt-checks.json")
    pool, receipts = read(pool_path), read(receipts_path)
    obligations_path = args.current_audit.with_name(args.current_audit.stem+"-terminal-obligations.json")
    if (len(pool) != current["joined_closed_full_type_codes_in_these_two_catalogues"]
            or len(receipts) != current["all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"]
            or normalized.get(str(pool_path.resolve())) != sha(pool_path)
            or normalized.get(str(receipts_path.resolve())) != sha(receipts_path)
            or normalized.get(str(obligations_path.resolve())) != sha(obligations_path)
            or sha(args.current_audit) != initial):
        raise ValueError("latest final lost historical types/receipts/terminals or its actual snapshot")
    if sha(__file__) != executed_digest or sha(accounting.__file__) != accounting_digest:
        raise ValueError("independent latest final executor or pure accounting changed during execution")
    report = {
        "schema": "N26-independent-latest-signed-grown-full134rod-current-final-rehash-v1",
        "all_current_file_digests_rehashed": True, "current_file_digests_rechecked": len(inventory),
        "current_audit_sha256": initial,
        "actual_own_geometry_publication_and_current_semantic_replays_equal": True,
        "independent_exact_root_and_newest_history_accounting": result,
        "candidate_angle_unresolved_closed_boxes": result["remaining_whole_roots"],
        "remaining_latest_partial_root_histories": result["remaining_latest_partial_histories"],
        "Rstar_conditional_frontier_pending_subtrees": current["Rstar_conditional_frontier_pending_subtrees"],
        "retained_closed_full_type_codes": len(pool), "retained_checked_proof_receipts": len(receipts),
        "radius_scope": current["radius_scope"], "r_strict_interval": current["r_strict_interval"],
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_checker_sha256": executed_digest,
        "executed_pure_accounting_sha256": accounting_digest,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
