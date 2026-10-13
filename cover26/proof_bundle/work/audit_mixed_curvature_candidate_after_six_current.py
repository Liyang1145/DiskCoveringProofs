"""Distinct current admission of actual mixed covers after the completed SIX pair.

The old compositor and sealed identity helpers are not edited or patched.
This executor explicitly uses the tested SIX ancestry adapter and executes
the actual frozen mixed main, including its complete model/history source.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_candidate_identity_after_six_target as identity
import n26_mixed_after_six_current_accounting as accounting
import verify_conditional_force_stage as binding
import verify_current_candidate_mixed_curvature_covers as overlay


def rehash(inventory, phase):
    normalized = {str(binding.local_path(text).resolve()): value
                  for text, value in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("mixed-after-SIX inventory has duplicate normalized paths")
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("mixed-after-SIX dependency changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({"mixed_after_six_phase": phase,
                              "digests_rehashed": number, "total": len(inventory)}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-final", "frontier", "overlay",
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
        raise FileExistsError("mixed-after-SIX admission requires entirely fresh outputs")
    executor_paths = (
        Path(__file__), Path(identity.__file__), Path(accounting.__file__),
        Path(overlay.__file__),
        Path(__file__).with_name("recheck_mixed_curvature_candidate_after_six_current.py"),
        Path(__file__).with_name("test_mixed_after_six_current_accounting.py"),
        Path(__file__).with_name("test_candidate_identity_after_six_target.py"),
        Path(__file__).with_name("recheck_mixed_curvature_candidate_current.py"),
    )
    executor_snapshot = {linux(path): binding.sha(path) for path in executor_paths}
    parent_digest = binding.sha(args.parent_audit)
    final_digest = binding.sha(args.parent_final)
    frontier_digest = binding.sha(args.frontier)
    parent, parent_final = binding.read(args.parent_audit), binding.read(args.parent_final)
    frontier = binding.read(args.frontier)
    accounting.parent_gate(
        parent, parent_digest, parent_final, frontier, args.frontier, frontier_digest,
    )
    six_final_checker = Path(__file__).with_name("recheck_six_target_source_current.py")
    if (
        parent_final["executed_checker_sha256"] != binding.sha(six_final_checker)
        or parent["files"].get(linux(six_final_checker)) != binding.sha(six_final_checker)
    ):
        raise ValueError("mixed-after-SIX parent final did not execute the bound actual SIX final")
    inventory = dict(parent["files"])
    rehash(inventory, "actual-completed-SIX-parent")
    accepted, paths = binding.bound(args.overlay)
    manifest = binding.read(args.overlay / "MANIFEST.json")
    proof_path = binding.local_path(manifest["parent_current_audit"])
    proof_parent = binding.read(proof_path)
    if (
        accepted["schema"] != overlay.SCHEMA
        or accepted["executed_checker_file"] != overlay.CHECKER
        or accepted["executed_checker_sha256"] != accepted["files"][overlay.CHECKER]
        or binding.sha(args.overlay / overlay.CHECKER) != accepted["executed_checker_sha256"]
        or binding.sha(overlay.__file__) != accepted["executed_checker_sha256"]
        or binding.read(args.overlay_replay) != accepted
        or binding.sha(args.overlay_replay) != binding.sha(args.overlay / "VERIFIED.json")
        or accepted["source_actual_remaining_candidate_roots"] != parent["candidate_angle_unresolved_closed_boxes"]
        or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
        or accepted["accepted_curvature_modes"] != overlay.MODES
        or len(accepted["negative_controls_rejected"]) != 29
    ):
        raise ValueError("mixed-after-SIX changed actual own executor/publication/mode controls")
    source = binding.local_path(manifest["source"])
    layer = identity.gate(parent, parent_digest, source)
    regression = binding.read(args.identity_regression)
    snapshot = regression["actual_old_source_layer_identity_snapshot"]
    if (
        regression["tested_identity_module_sha256"] != binding.sha(identity.__file__)
        or regression["executed_test_sha256"] != binding.sha(
            Path(__file__).with_name("test_candidate_identity_after_six_target.py"))
        or len(regression["synthetic_invalid_six_schema_ancestry_controls_rejected"]) != 20
        or regression["synthetic_six_header_NOT_completed_current_or_geometry_acceptance"] is not True
        or regression["verified"] is not False or regression["new_geometric_payments"] != 0
        or any(snapshot[key] != layer[key] for key in (
            "actual_latest_candidate_acceptance", "actual_latest_candidate_acceptance_sha256",
            "actual_latest_candidate_pending_angles", "actual_latest_candidate_pending_angles_sha256",
            "actual_remaining_candidate_whole_roots",
        ))
    ):
        raise ValueError("mixed-after-SIX ancestry regression changed actual source or became fake geometry")
    if (
        binding.sha(proof_path) != accepted["parent_current_audit_sha256"]
        or inventory.get(linux(proof_path)) != binding.sha(proof_path)
        or any(inventory.get(text) != digest for text, digest in proof_parent["files"].items())
        or proof_parent["r_strict_interval"] != parent["r_strict_interval"]
        or accepted["actual_latest_candidate_layer_identity"]["actual_latest_candidate_acceptance_sha256"]
        != layer["actual_latest_candidate_acceptance_sha256"]
        or accepted["actual_latest_candidate_layer_identity"]["actual_latest_candidate_pending_angles_sha256"]
        != layer["actual_latest_candidate_pending_angles_sha256"]
    ):
        raise ValueError("mixed proof-time source is not the identical actually bound SIX candidate ancestor")
    controls = binding.read(args.accounting_regression)
    if (
        controls["schema"] != "N26-mixed-after-six-synthetic-current-accounting-controls-v1"
        or controls["verified"] is not False or controls["new_geometric_payments"] != 0
        or controls["tested_accounting_sha256"] != binding.sha(accounting.__file__)
        or controls["tested_pure_root_accounting_sha256"] != binding.sha(accounting.old_final.__file__)
        or controls["executed_test_sha256"] != binding.sha(
            Path(__file__).with_name("test_mixed_after_six_current_accounting.py"))
        or len(controls["invalid_controls_rejected"]) != accounting.CONTROL_COUNT
        or controls["actual_mixed_acceptance_sha256"] != binding.sha(args.overlay / "VERIFIED.json")
        or controls["actual_six_geometry_frontier_sha256"] != frontier_digest
        or controls["synthetic_parent_and_current_headers_NOT_actual_admission"] is not True
    ):
        raise ValueError("mixed-after-SIX root/frontier preservation controls missing or changed")
    command = [
        sys.executable, str(args.overlay / overlay.CHECKER),
        "--input", str(args.overlay), "--report", str(semantic_path),
    ]
    print("Executing the ENTIRE frozen mixed source/model/history checker and all 29 controls.",
          flush=True)
    executed = subprocess.run(command, check=False)
    if executed.returncode:
        raise ValueError("mixed-after-SIX full semantics failed; partial evidence retained")
    if (
        binding.read(semantic_path) != accepted
        or binding.sha(semantic_path) != binding.sha(args.overlay / "VERIFIED.json")
        or binding.sha(args.parent_audit) != parent_digest
        or binding.sha(args.parent_final) != final_digest
        or binding.read(args.overlay / "MANIFEST.json") != manifest
        or identity.gate(parent, parent_digest, source) != layer
    ):
        raise ValueError("mixed-after-SIX source/current/actual semantic replay changed")
    incoming = binding.read(args.overlay / "SOURCE-PENDING-ANGLES.json")
    payments = binding.read(args.overlay / "ROOT-PAYMENTS.json")
    remaining = binding.read(args.overlay / "PENDING-ANGLES.json")
    history = binding.read(args.overlay / "SOURCE-ROOT-HISTORY.json")
    retained = binding.read(args.overlay / "REMAINING-ROOT-HISTORY.json")
    indices = binding.read(args.overlay / "CERTIFICATE.json")["discharged_actual_source_root_indices"]
    pool_path = args.parent_audit.with_name(args.parent_audit.stem + suffixes[0])
    receipt_path = args.parent_audit.with_name(args.parent_audit.stem + suffixes[1])
    terminal_path = args.parent_audit.with_name(args.parent_audit.stem + suffixes[2])
    for path in (pool_path, receipt_path, terminal_path):
        if inventory.get(linux(path)) != binding.sha(path):
            raise ValueError("mixed-after-SIX lost actual historical pool/receipts/terminal ownership")
    pool = binding.read(pool_path)
    receipts = historical.retained_pool_gate(pool, parent, F(accepted["radius_upper"]))
    if len(pool) != 87 or len(receipts) != 215 or binding.read(receipt_path) != receipts:
        raise ValueError("mixed-after-SIX changed the actual 87-type/215-receipt proof pool")
    for suffix, original in zip(suffixes, (pool_path, receipt_path, terminal_path)):
        target = args.output.with_name(args.output.stem + suffix)
        with target.open("xb") as output:
            output.write(original.read_bytes())
        paths.append(target)
    paths.extend((
        args.parent_audit, args.parent_final, args.frontier, args.overlay_replay,
        args.narrative, semantic_path, args.identity_regression, args.accounting_regression,
        *executor_paths,
        Path(identity.previous.__file__), Path(identity.previous.original.__file__),
        Path(__file__).with_name("n26_current_mixed_curvature_candidate_source.py"),
        Path(__file__).with_name("n26-mixed-curvature-supplemental-acceptance-proof.md"),
        Path(__file__).with_name("run_mixed_after_six_serial_current_final_v1.ps1"),
        Path(__file__).with_name("run_mixed_after_six_after_live_predecessor_v1.ps1"),
    ))
    distinct = {linux(Path(path)): Path(path) for path in paths}
    for text, path in distinct.items():
        digest = binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("mixed-after-SIX inherited/new inventories disagree: " + text)
        inventory[text] = digest
    rehash(inventory, "merged-current-after-real-semantics")
    if (
        binding.sha(args.parent_audit) != parent_digest
        or binding.sha(args.parent_final) != final_digest
        or binding.sha(args.frontier) != frontier_digest
        or binding.read(args.frontier) != frontier
        or any(binding.sha(path) != digest for path, digest in executor_snapshot.items())
    ):
        raise ValueError("mixed-after-SIX current parent/frontier/execution modules changed")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": accounting.CURRENT_SCHEMA,
        "prior_current_audit_sha256": parent_digest,
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "mixed_after_six_actual_completed_parent_pair_bound": True,
        "mixed_after_six_parent_audit_file": linux(args.parent_audit),
        "mixed_after_six_parent_final_file": linux(args.parent_final),
        "mixed_after_six_parent_final_sha256": final_digest,
        "mixed_after_six_frontier_sha256": frontier_digest,
        "mixed_after_six_identity_adapter_file": linux(Path(identity.__file__)),
        "mixed_after_six_identity_adapter_sha256": executor_snapshot[linux(Path(identity.__file__))],
        "mixed_after_six_accounting_controls_file": linux(args.accounting_regression),
        "mixed_after_six_identity_controls_file": linux(args.identity_regression),
        "mixed_after_six_overlay_folder": linux(args.overlay),
        "mixed_after_six_overlay_publication_file": linux(args.overlay_replay),
        "inherited_six_target_candidate_unchanged_flag_is_historical_NOT_current_root_count": True,
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
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "current_transport_frontier_unchanged_by_mixed_candidate_covers": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "candidate_transport_global_lower_bound_proved": False,
        "executed_current_mixed_admission_file": linux(Path(__file__)),
        "executed_current_mixed_admission_sha256": executor_snapshot[linux(Path(__file__))],
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory,
    })
    accounting.source_partition_gate(
        report, accepted, incoming, payments, remaining, history, retained, indices,
    )
    accounting.current_gate(report, parent, parent_digest, frontier, frontier_digest)
    with args.output.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "mixed_after_six_current_admission_passed": True,
        "new_whole_candidate_roots": 9, "remaining_whole_candidate_roots": 16,
        "actual_six_frontier_retained": 5637,
        "bound_current_files": len(inventory), "independent_final_STILL_required": True,
        "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
