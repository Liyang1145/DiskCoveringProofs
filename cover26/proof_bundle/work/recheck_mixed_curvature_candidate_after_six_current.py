"""Independent final binding and exact accounting for mixed-after-SIX current.

This does not rerun the compositor. It rehashes the complete merged inventory,
checks the actual completed parent pair, exact unchanged SIX frontier,
source-root/history partition, semantic execution identity and retained
87-type/215-receipt pool. It cannot claim unrestricted/global completion.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

import n26_candidate_identity_after_six_target as identity
import n26_mixed_after_six_current_accounting as accounting


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
    if current["schema"] != accounting.CURRENT_SCHEMA:
        raise ValueError("independent mixed-after-SIX final received another current schema")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): value for text, value in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("mixed-after-SIX final has duplicate normalized paths")

    def bound(path):
        if normalized.get(str(local_path(path).resolve())) != sha(path):
            raise ValueError("mixed-after-SIX final input/executor not bound: " + str(path))

    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("mixed-after-SIX final dependency changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({"mixed_after_six_final_digests_rehashed": number,
                              "total": len(inventory)}), flush=True)
    parent_path = local_path(current["mixed_after_six_parent_audit_file"])
    parent_final_path = local_path(current["mixed_after_six_parent_final_file"])
    frontier_path = local_path(current["current_frontier_actual_file"])
    for path in (parent_path, parent_final_path, frontier_path):
        bound(path)
    parent_digest, parent_final_digest = sha(parent_path), sha(parent_final_path)
    parent, parent_final = read(parent_path), read(parent_final_path)
    frontier_digest, frontier = sha(frontier_path), read(frontier_path)
    accounting.parent_gate(
        parent, parent_digest, parent_final, frontier, frontier_path, frontier_digest,
    )
    accounting.current_gate(current, parent, parent_digest, frontier, frontier_digest)
    if (
        current["mixed_after_six_parent_final_sha256"] != parent_final_digest
        or current["prior_current_file_digests_rechecked"] != len(parent["files"])
        or current["inherited_six_target_candidate_unchanged_flag_is_historical_NOT_current_root_count"] is not True
    ):
        raise ValueError("mixed-after-SIX final changed parent pair or historical SIX event labels")
    six_final_checker = Path(__file__).with_name("recheck_six_target_source_current.py")
    bound(six_final_checker)
    if parent_final["executed_checker_sha256"] != sha(six_final_checker):
        raise ValueError("mixed-after-SIX final lacks the actual independent SIX final executor")
    if (
        local_path(current["mixed_after_six_overlay_folder"]).resolve() != args.overlay.resolve()
        or local_path(current["mixed_after_six_overlay_publication_file"]).resolve() != args.overlay_replay.resolve()
        or local_path(current["actual_current_candidate_acceptance"]).resolve()
        != (args.overlay / "VERIFIED.json").resolve()
        or local_path(current["actual_current_candidate_pending_angles"]).resolve()
        != (args.overlay / "PENDING-ANGLES.json").resolve()
        or local_path(current["actual_current_candidate_remaining_history"]).resolve()
        != (args.overlay / "REMAINING-ROOT-HISTORY.json").resolve()
    ):
        raise ValueError("mixed-after-SIX final changed actual overlay/root/history ownership")
    manifest = read(args.overlay / "MANIFEST.json")
    source = local_path(manifest["source"])
    accepted = read(args.overlay / "VERIFIED.json")
    semantic_path = local_path(current["mixed_curvature_semantic_replay_file"])
    checker = args.overlay / "verify_current_candidate_mixed_curvature_covers.py"
    command = current["mixed_curvature_actual_full_semantic_command"]
    if (
        accepted["schema"] != "N26-accepted-current-mixed-curvature-LOCAL-root-covers-v1"
        or accepted["verified"] is not True
        or read(args.overlay_replay) != accepted or read(semantic_path) != accepted
        or sha(args.overlay_replay) != sha(args.overlay / "VERIFIED.json")
        or sha(semantic_path) != sha(args.overlay / "VERIFIED.json")
        or accepted["executed_checker_file"] != checker.name
        or accepted["executed_checker_sha256"] != accepted["files"][checker.name]
        or sha(checker) != accepted["executed_checker_sha256"]
        or len(command) != 6
        or local_path(command[0]).resolve() != Path(sys.executable).resolve()
        or local_path(command[1]).resolve() != checker.resolve()
        or command[2] != "--input" or local_path(command[3]).resolve() != args.overlay.resolve()
        or command[4] != "--report" or local_path(command[5]).resolve() != semantic_path.resolve()
    ):
        raise ValueError("mixed-after-SIX final own/publication/full-main semantic execution disagree")
    layer = identity.gate(parent, parent_digest, source, reader=read, hasher=sha)
    if layer != current["mixed_curvature_actual_source_layer_identity"]:
        raise ValueError("mixed-after-SIX final actual latest SIX candidate ancestry changed")
    # Also require that the output schema selects the new 16-root layer, not
    # the 25-root source. This is identity only, not new geometry acceptance.
    result_identity = identity.gate(current, initial, args.overlay, reader=read, hasher=sha)
    if result_identity["actual_remaining_candidate_whole_roots"] != 16:
        raise ValueError("mixed-after-SIX final failed to advance the exact candidate owner")
    incoming = read(args.overlay / "SOURCE-PENDING-ANGLES.json")
    payments = read(args.overlay / "ROOT-PAYMENTS.json")
    remaining = read(args.overlay / "PENDING-ANGLES.json")
    history = read(args.overlay / "SOURCE-ROOT-HISTORY.json")
    retained = read(args.overlay / "REMAINING-ROOT-HISTORY.json")
    indices = read(args.overlay / "CERTIFICATE.json")["discharged_actual_source_root_indices"]
    accounting.source_partition_gate(
        current, accepted, incoming, payments, remaining, history, retained, indices,
    )
    if incoming != read(source / "PENDING-ANGLES.json"):
        raise ValueError("mixed-after-SIX final replaced the exact actual latest incoming root rows")
    proof_path = local_path(manifest["parent_current_audit"])
    bound(proof_path)
    proof_parent = read(proof_path)
    if (
        sha(proof_path) != accepted["parent_current_audit_sha256"]
        or proof_parent["r_strict_interval"] != parent["r_strict_interval"]
        or any(inventory.get(text) != value for text, value in proof_parent["files"].items())
    ):
        raise ValueError("mixed-after-SIX final lost the actual full proof-time source ancestor")
    for name, digest in accepted["files"].items():
        path = args.overlay / name
        bound(path)
        if sha(path) != digest:
            raise ValueError("mixed-after-SIX actual acceptance inventory changed: " + name)
    paths = (
        args.overlay / "VERIFIED.json", args.overlay_replay, semantic_path,
        source / "VERIFIED.json", source / "PENDING-ANGLES.json",
        Path(__file__), Path(identity.__file__), Path(accounting.__file__),
        Path(accounting.old_final.__file__),
        Path(identity.previous.__file__), Path(identity.previous.original.__file__),
    )
    for path in paths:
        bound(path)
    adapter_path = local_path(current["mixed_after_six_identity_adapter_file"])
    if (
        adapter_path.resolve() != Path(identity.__file__).resolve()
        or sha(adapter_path) != current["mixed_after_six_identity_adapter_sha256"]
    ):
        raise ValueError("mixed-after-SIX final changed its explicit tested SIX adapter")
    executor_path = local_path(current["executed_current_mixed_admission_file"])
    bound(executor_path)
    if (
        executor_path.resolve() != Path(__file__).with_name(
            "audit_mixed_curvature_candidate_after_six_current.py").resolve()
        or sha(executor_path) != current["executed_current_mixed_admission_sha256"]
    ):
        raise ValueError("mixed-after-SIX final mislabeled the actual new current executor")
    pool, receipts = None, None
    for suffix in ("-closed-type-pool.json", "-closed-receipt-checks.json",
                   "-terminal-obligations.json"):
        new_path = args.current_audit.with_name(args.current_audit.stem + suffix)
        old_path = parent_path.with_name(parent_path.stem + suffix)
        bound(new_path)
        bound(old_path)
        if sha(new_path) != sha(old_path):
            raise ValueError("mixed-after-SIX final changed historical pool/receipt/terminal bytes")
        if suffix == "-closed-type-pool.json":
            pool = read(new_path)
        elif suffix == "-closed-receipt-checks.json":
            receipts = read(new_path)
    if len(pool) != 87 or len(receipts) != 215:
        raise ValueError("mixed-after-SIX final lost historical type/proof receipt closure")
    if (
        sha(args.current_audit) != initial or sha(parent_path) != parent_digest
        or sha(parent_final_path) != parent_final_digest or sha(frontier_path) != frontier_digest
    ):
        raise ValueError("mixed-after-SIX current/parent/frontier changed during independent final")
    report = {
        "schema": accounting.FINAL_SCHEMA,
        "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": len(inventory), "current_audit_sha256": initial,
        "actual_completed_SIX_parent_pair_AND_identical_filtered_frontier_bound": True,
        "mixed_actual_own_acceptance_publication_and_current_semantic_replays_equal": True,
        "actual_NEW_current_executor_AND_tested_SIX_identity_adapter_bound": True,
        "new_complete_candidate_source_roots_lower_bounded": len(payments),
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "all_uncovered_whole_roots_and_latest_partial_histories_retained": True,
        "remaining_latest_partial_root_histories": len(retained),
        "actual_current_candidate_layer_identity": result_identity,
        "Rstar_conditional_frontier_pending_subtrees": 5637,
        "Rstar_conditional_frontier_families": frontier["families"],
        "retained_closed_full_type_codes": len(pool), "retained_checked_proof_receipts": len(receipts),
        "radius_scope": current["radius_scope"], "r_strict_interval": current["r_strict_interval"],
        "original_U_frontier_nodes_removed": 0, "original_LOCAL_unchanged": "7/800000",
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_checker_sha256": sha(__file__),
        "executed_accounting_sha256": sha(accounting.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("Rstar_conditional_frontier_families",
                                     "actual_current_candidate_layer_identity")}), flush=True)


if __name__ == "__main__":
    main()
