"""Admit actually replayed mixed-curvature covers into the complete current chain.

The frozen overlay checker is executed as a separate subprocess, including
its COMPLETE owned source/model/history gate and all twenty-nine controls.
This auditor preserves the transport frontier and historical proof pool.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_candidate_identity_with_mixed_curvature as identity
import verify_conditional_force_stage as binding
import verify_current_candidate_mixed_curvature_covers as overlay


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-digest-recheck", "frontier", "overlay",
                 "overlay-replay", "narrative", "identity-regression",
                 "accounting-regression", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    semantic_path = args.output.with_name(args.output.stem + "-overlay-semantic-replay.json")
    suffixes = ("-closed-type-pool.json", "-closed-receipt-checks.json",
                "-terminal-obligations.json")
    targets = [args.output, semantic_path,
               *(args.output.with_name(args.output.stem + suffix) for suffix in suffixes)]
    if any(path.exists() for path in targets):
        raise FileExistsError("mixed current admission requires entirely fresh outputs")
    parent_digest = binding.sha(args.parent_audit)
    parent, rehash = binding.read(args.parent_audit), binding.read(args.parent_digest_recheck)
    if (parent["current_bound_bytes_rechecked"] is not True
            or parent["prior_completed_full_chain_semantic_replay_still_bound"] is not True
            or parent["radius_scope"] != binding.SCOPE
            or parent["global_optimality_proved"] is not False
            or rehash["current_audit_sha256"] != parent_digest
            or rehash["all_current_file_digests_rehashed"] is not True
            or rehash["current_file_digests_rechecked"] != len(parent["files"])
            or rehash["candidate_angle_unresolved_closed_boxes"]
            != parent["candidate_angle_unresolved_closed_boxes"]):
        raise ValueError("mixed current admission lacks the actual completed parent/final pair")
    inventory = dict(parent["files"])
    print("Rehashing every actual current transport/candidate dependency.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("mixed current parent dependency changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({"parent_digests_checked": number, "total": len(inventory)}), flush=True)
    frontier = binding.read(args.frontier)
    if (inventory.get(linux(args.frontier)) != binding.sha(args.frontier)
            or len(frontier["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or frontier["radius_scope"] != binding.SCOPE
            or F(frontier["radius_upper"]) != F(parent["r_strict_interval"][1])):
        raise ValueError("mixed current admission changed the actual global transport frontier")
    accepted, paths = binding.bound(args.overlay)
    manifest = binding.read(args.overlay / "MANIFEST.json")
    proof_path = binding.local_path(manifest["parent_current_audit"])
    proof_parent = binding.read(proof_path)
    if (accepted["schema"] != overlay.SCHEMA
            or accepted["executed_checker_file"] != overlay.CHECKER
            or accepted["executed_checker_sha256"] != accepted["files"][overlay.CHECKER]
            or binding.sha(args.overlay / overlay.CHECKER) != accepted["executed_checker_sha256"]
            or binding.sha(overlay.__file__) != accepted["executed_checker_sha256"]
            or binding.read(args.overlay_replay) != accepted
            or accepted["source_actual_remaining_candidate_roots"]
            != parent["candidate_angle_unresolved_closed_boxes"]
            or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
            or accepted["accepted_curvature_modes"] != overlay.MODES
            or len(accepted["negative_controls_rejected"]) != 29):
        raise ValueError("mixed current admission changed actual own executor/replay/mode controls")
    source = binding.local_path(manifest["source"])
    layer = identity.gate(parent, parent_digest, source)
    regression = binding.read(args.identity_regression)
    snapshot = regression["actual_old_schema_delegation_identity_snapshot"]
    if (regression["tested_identity_module_sha256"] != binding.sha(identity.__file__)
            or regression["executed_test_sha256"] != binding.sha(
                Path(__file__).with_name("test_candidate_identity_with_mixed_curvature.py"))
            or len(regression["synthetic_invalid_identity_controls_rejected"]) != 16
            or regression["actual_snapshot_is_identity_only_NOT_geometry_or_final_current_adoption"] is not True
            or regression["new_geometric_payments"] != 0
            or snapshot["actual_latest_candidate_acceptance"]
            != layer["actual_latest_candidate_acceptance"]
            or snapshot["actual_latest_candidate_acceptance_sha256"]
            != layer["actual_latest_candidate_acceptance_sha256"]
            or snapshot["actual_latest_candidate_pending_angles_sha256"]
            != layer["actual_latest_candidate_pending_angles_sha256"]):
        raise ValueError("mixed actual-latest identity regression missing or used another source")
    if (binding.sha(proof_path) != accepted["parent_current_audit_sha256"]
            or (proof_parent != parent and (
                inventory.get(linux(proof_path)) != binding.sha(proof_path)
                or any(inventory.get(text) != digest for text, digest in proof_parent["files"].items())))
            or proof_parent["r_strict_interval"] != parent["r_strict_interval"]):
        raise ValueError("mixed proof-time source is not an identical bound current ancestor")
    command = [
        sys.executable, str(args.overlay / overlay.CHECKER),
        "--input", str(args.overlay), "--report", str(semantic_path),
    ]
    print("Executing the ENTIRE frozen overlay checker, original source gate and all controls.",
          flush=True)
    executed = subprocess.run(command, check=False)
    if executed.returncode:
        raise ValueError("mixed full current semantic replay failed; partial outputs retained")
    if (binding.read(semantic_path) != accepted
            or binding.sha(args.parent_audit) != parent_digest
            or binding.read(args.overlay / "MANIFEST.json") != manifest):
        raise ValueError("mixed actual current semantic replay or source identity changed")
    incoming = binding.read(args.overlay / "SOURCE-PENDING-ANGLES.json")
    payments = binding.read(args.overlay / "ROOT-PAYMENTS.json")
    remaining = binding.read(args.overlay / "PENDING-ANGLES.json")
    retained = binding.read(args.overlay / "REMAINING-ROOT-HISTORY.json")
    indices = binding.read(args.overlay / "CERTIFICATE.json")["discharged_actual_source_root_indices"]
    if (len(set(indices)) != len(indices)
            or [row["source_OPEN_index"] for row in payments] != indices
            or [row for row in incoming if row["index"] not in indices] != remaining
            or len(payments) + len(remaining) != len(incoming)
            or len(payments) != accepted["new_whole_candidate_source_roots_lower_bounded"]
            or len(remaining) != accepted["unresolved_closed_angle_boxes"]
            or len(retained) != accepted["remaining_root_partial_histories_retained"]
            or any(not row["source_candidate_root_fully_lower_bounded"]
                   or row["source_candidate_root_strictly_empty"] for row in payments)):
        raise ValueError("mixed current admission lost roots or falsely emptied LOCAL equality")
    accounting_regression = binding.read(args.accounting_regression)
    if (accounting_regression["synthetic_exact_source_row_and_latest_history_partition_passed"] is not True
            or len(accounting_regression["invalid_accounting_controls_rejected"]) != 12
            or accounting_regression["verified"] is not False
            or accounting_regression["new_geometric_payments"] != 0
            or accounting_regression["tested_final_rehash_executor_sha256"] != binding.sha(
                Path(__file__).with_name("recheck_mixed_curvature_candidate_current.py"))
            or accounting_regression["executed_test_sha256"] != binding.sha(
                Path(__file__).with_name("test_mixed_curvature_final_accounting.py"))):
        raise ValueError("mixed final root/history accounting controls missing or changed")
    pool_path = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    terminal_path = args.parent_audit.with_name(args.parent_audit.stem + "-terminal-obligations.json")
    if (inventory.get(linux(pool_path)) != binding.sha(pool_path)
            or inventory.get(linux(terminal_path)) != binding.sha(terminal_path)):
        raise ValueError("mixed current admission lost actual historical pool/terminal ownership")
    pool = binding.read(pool_path)
    receipts = historical.retained_pool_gate(pool, parent, F(accepted["radius_upper"]))
    for suffix, data in (
        (suffixes[0], pool), (suffixes[1], receipts),
        (suffixes[2], binding.read(terminal_path)),
    ):
        target = args.output.with_name(args.output.stem + suffix)
        if suffix == suffixes[0]:
            with target.open("xb") as output:
                output.write(pool_path.read_bytes())
        else:
            with target.open("x", encoding="utf-8", newline="\n") as output:
                output.write(json.dumps(data, indent=2) + "\n")
        paths.append(target)
    paths.extend((
        args.parent_audit, args.parent_digest_recheck, args.frontier,
        args.overlay_replay, args.narrative, semantic_path,
        Path(__file__), Path(overlay.__file__), Path(identity.__file__),
        args.identity_regression,
        Path(__file__).with_name("test_candidate_identity_with_mixed_curvature.py"),
        args.accounting_regression,
        Path(__file__).with_name("test_mixed_curvature_final_accounting.py"),
        Path(__file__).with_name("n26_current_mixed_curvature_candidate_source.py"),
        Path(__file__).with_name("recheck_mixed_curvature_candidate_current.py"),
        Path(__file__).with_name("n26-mixed-curvature-supplemental-acceptance-proof.md"),
    ))
    # Every DISTINCT dependency is still checked. Duplicate path references
    # from inherited proof layers are not separate byte/geometry obligations.
    distinct = {linux(Path(path)): Path(path) for path in paths}
    for text, path in distinct.items():
        digest = binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("mixed old and new bound inventories disagree: " + text)
        inventory[text] = digest
    print("Rehashing the final complete mixed current inventory.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("mixed final current dependency changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({"mixed_current_digests_checked": number,
                              "total": len(inventory)}), flush=True)
    if (binding.sha(args.parent_audit) != parent_digest
            or binding.read(args.frontier) != frontier):
        raise ValueError("mixed current parent or global transport partition changed")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": identity.CURRENT_SCHEMA,
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": parent_digest,
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here": True,
        "mixed_curvature_source_is_actual_latest_candidate_layer": True,
        "mixed_curvature_actual_source_layer_identity": layer,
        "mixed_curvature_new_whole_source_roots_lower_bounded": len(payments),
        "mixed_curvature_new_strictly_empty_source_roots": 0,
        "mixed_curvature_new_source_roots_with_original_LOCAL": len(payments),
        "mixed_curvature_mode_root_counts": accepted["mode_root_counts"],
        "mixed_curvature_strict_energy_slabs": accepted["supplemental_strict_energy_slabs"],
        "mixed_curvature_actual_full_semantic_command": command,
        "mixed_curvature_actual_full_semantic_exit_code": executed.returncode,
        "mixed_curvature_semantic_replay_file": linux(semantic_path),
        "all_newest_owned_histories_retained_identically": True,
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "actual_current_candidate_acceptance": linux(args.overlay / "VERIFIED.json"),
        "actual_current_candidate_pending_angles": linux(args.overlay / "PENDING-ANGLES.json"),
        "actual_current_candidate_remaining_history": linux(args.overlay / "REMAINING-ROOT-HISTORY.json"),
        "remaining_latest_partial_root_histories": len(retained),
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "current_frontier_actual_file": linux(args.frontier),
        "current_transport_frontier_unchanged_by_mixed_candidate_covers": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "candidate_transport_global_lower_bound_proved": not remaining,
        "executed_current_mixed_admission_file": linux(Path(__file__)),
        "executed_current_mixed_admission_sha256": binding.sha(__file__),
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory,
    })
    with args.output.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "mixed_current_admission_passed": True, "new_whole_roots": len(payments),
        "remaining_whole_roots": len(remaining), "bound_current_files": len(inventory),
        "independent_final_rehash_still_required": True, "global_optimality_proved": False}),
        flush=True)


if __name__ == "__main__":
    main()
