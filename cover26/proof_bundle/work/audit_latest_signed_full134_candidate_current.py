"""Admit actual whole geometry to the complete latest current, never a DATA cache."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_candidate_identity_with_latest_signed_forests as identity
import n26_latest_signed_full134_current_accounting as accounting
import recheck_latest_signed_full134_candidate_current as final
import verify_conditional_force_stage as binding
import verify_latest_candidate_signed_full134rod_forests as overlay


def regressions_gate(identity_record, accounting_record, layer, source):
    snapshot = identity_record["actual_prior_schema_delegation_identity_snapshot"]
    if (identity_record["tested_identity_module_sha256"] != binding.sha(identity.__file__)
            or identity_record["executed_test_sha256"] != binding.sha(
                Path(__file__).with_name("test_latest_signed_full134_current_identity.py"))
            or len(identity_record["synthetic_invalid_latest_identity_controls_rejected"]) != 20
            or len(identity_record["synthetic_invalid_final_acceptance_controls_rejected"]) != 16
            or identity_record["tested_independent_final_executor_sha256"] != binding.sha(final.__file__)
            or identity_record["actual_snapshot_is_identity_only_NOT_geometry_or_current_adoption"] is not True
            or identity_record["synthetic_latest_receipt_shapes_NOT_an_actual_geometry_acceptance"] is not True
            or identity_record["verified"] is not False or identity_record["new_geometric_payments"] != 0
            or any(snapshot[name] != layer[name] for name in (
                "actual_latest_candidate_acceptance", "actual_latest_candidate_acceptance_sha256",
                "actual_latest_candidate_pending_angles_sha256"))):
        raise ValueError("latest current lacks actual-source identity and own independent-final guards")
    if (accounting_record["tested_pure_final_accounting_sha256"] != binding.sha(accounting.__file__)
            or accounting_record["executed_test_sha256"] != binding.sha(
                Path(__file__).with_name("test_latest_signed_full134_current_accounting.py"))
            or len(accounting_record["actual_invalid_root_history_ledger_count_and_scope_controls_rejected"]) != 21
            or accounting_record["actual_source_acceptance_DATA_sha256"] != binding.sha(source / "VERIFIED.json")
            or accounting_record["actual_source_pending_DATA_sha256"] != binding.sha(source / "PENDING-ANGLES.json")
            or accounting_record["synthetic_final_shapes_are_NOT_geometry_acceptance_or_current_adoption"] is not True
            or accounting_record["actual_grown_v9_NOT_replaced_by_v8_or_old_fixture"] is not True
            or accounting_record["ENTIRE_source_model_forest_geometry_and_complete_current_join_NOT_executed"] is not True
            or accounting_record["verified"] is not False or accounting_record["new_geometric_payments"] != 0):
        raise ValueError("latest current lacks this actual source's independent exact history accounting controls")


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-digest-recheck", "frontier", "overlay", "overlay-replay",
                 "narrative", "identity-regression", "accounting-regression", "output"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    semantic_path = args.output.with_name(args.output.stem+"-overlay-semantic-replay.json")
    suffixes = ("-closed-type-pool.json", "-closed-receipt-checks.json", "-terminal-obligations.json")
    if any(path.exists() for path in (
            args.output, semantic_path,
            *(args.output.with_name(args.output.stem+suffix) for suffix in suffixes))):
        raise FileExistsError("latest complete-current adoption needs entirely fresh targets")
    executed_digest = binding.sha(__file__)
    helper_digests = {Path(module.__file__): binding.sha(module.__file__)
                      for module in (identity, accounting, final, overlay, historical)}
    parent_digest = binding.sha(args.parent_audit)
    parent, rehash = binding.read(args.parent_audit), binding.read(args.parent_digest_recheck)
    overlay.source_backend.pair_gate(parent, rehash, parent_digest)
    inventory = dict(parent["files"])
    print("Rehashing EVERY actual completed current dependency before latest forest adoption.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("latest current parent dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"latest_parent_digests_rechecked": number, "total": len(inventory)}), flush=True)
    frontier = binding.read(args.frontier)
    if (inventory.get(linux(args.frontier)) != binding.sha(args.frontier)
            or len(frontier["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or frontier["radius_scope"] != binding.SCOPE
            or F(frontier["radius_upper"]) != F(parent["r_strict_interval"][1])):
        raise ValueError("latest partial forests cannot drop or change the actual transport frontier")
    accepted, paths = binding.bound(args.overlay)
    manifest = binding.read(args.overlay / "MANIFEST.json")
    source = binding.local_path(manifest["source"])
    layer = identity.gate(parent, parent_digest, source)
    regressions_gate(binding.read(args.identity_regression), binding.read(args.accounting_regression), layer, source)
    if (accepted["schema"] != overlay.SCHEMA or accepted["verified"] is not True
            or accepted["executed_checker_file"] != overlay.CHECKER
            or accepted["executed_checker_sha256"] != accepted["files"][overlay.CHECKER]
            or binding.sha(args.overlay / overlay.CHECKER) != accepted["executed_checker_sha256"]
            or binding.sha(overlay.__file__) != accepted["executed_checker_sha256"]
            or binding.read(args.overlay_replay) != accepted
            or accepted["source_actual_remaining_candidate_roots"] != parent["candidate_angle_unresolved_closed_boxes"]
            or accepted["source_acceptance_sha256"] != layer["actual_latest_candidate_acceptance_sha256"]
            or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
            or accepted["accepted_forest_modes"] != overlay.MODES
            or len(accepted["negative_controls_rejected"]) != 21
            or accepted["actual_full_source_replay"][
                "ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here"] is not True):
        raise ValueError("latest current requires ACTUAL own full geometry/publication and genuinely current source")
    proof_path = binding.local_path(manifest["formal_current"])
    proof_final_path = binding.local_path(manifest["formal_final"])
    proof_parent = binding.read(proof_path)
    if (binding.sha(proof_path) != manifest["formal_current_sha256"]
            or binding.sha(proof_final_path) != manifest["formal_final_sha256"]
            or proof_parent["r_strict_interval"] != parent["r_strict_interval"]
            or proof_parent["candidate_angle_unresolved_closed_boxes"]
            != parent["candidate_angle_unresolved_closed_boxes"]
            or (proof_path.resolve() != args.parent_audit.resolve() and (
                inventory.get(linux(proof_path)) != binding.sha(proof_path)
                or inventory.get(linux(proof_final_path)) != binding.sha(proof_final_path)
                or any(inventory.get(text) != digest for text, digest in proof_parent["files"].items())))):
        raise ValueError("latest whole geometry proof-time pair is not an identically bound current ancestor")
    command = [sys.executable, str(args.overlay / overlay.CHECKER),
               "--input", str(args.overlay), "--report", str(semantic_path)]
    print("Executing AGAIN the ENTIRE actual frozen source/model/history/forest geometry main.", flush=True)
    executed = subprocess.run(command, check=False)
    if executed.returncode:
        raise ValueError("latest complete-current semantic geometry failed; preserve all partial evidence")
    if (binding.read(semantic_path) != accepted
            or binding.sha(args.parent_audit) != parent_digest
            or binding.read(args.overlay / "MANIFEST.json") != manifest):
        raise ValueError("latest full semantic replay, actual parent or frozen input changed")
    incoming = binding.read(args.overlay / "SOURCE-PENDING-ANGLES.json")
    payments = binding.read(args.overlay / "ROOT-PAYMENTS.json")
    remaining = binding.read(args.overlay / "PENDING-ANGLES.json")
    retained = binding.read(args.overlay / "REMAINING-ROOT-HISTORY.json")
    records = {25: binding.read(args.overlay / "ROOT25-DIAGNOSIS.json"),
               28: binding.read(args.overlay / "ROOT28-GROWN-DIAGNOSIS.json")}
    seeds = {25: binding.read(args.overlay / "ROOT25-SEED.json"), 28: binding.read(args.overlay / "ROOT28-V8.json")}
    temporary = {
        **parent, "schema": identity.CURRENT_SCHEMA,
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "latest_forest_new_whole_source_roots_lower_bounded": len(payments),
        "remaining_latest_partial_root_histories": len(retained),
    }
    accounted = accounting.gate(
        temporary, accepted, incoming, binding.read(args.overlay / "SOURCE-ROOT-HISTORY.json"),
        records, seeds, binding.read(args.overlay / "ROOT-CLASSIFICATION.json"),
        payments, remaining, retained, binding.read(args.overlay / "LOWER-LEDGER.json"))
    pool_path = args.parent_audit.with_name(args.parent_audit.stem+"-closed-type-pool.json")
    terminal_path = args.parent_audit.with_name(args.parent_audit.stem+"-terminal-obligations.json")
    if (inventory.get(linux(pool_path)) != binding.sha(pool_path)
            or inventory.get(linux(terminal_path)) != binding.sha(terminal_path)):
        raise ValueError("latest adoption lost actual closed-type pool or complete terminal ownership")
    pool = binding.read(pool_path)
    receipts = historical.retained_pool_gate(pool, parent, F(accepted["radius_upper"]))
    for suffix, data in (
        (suffixes[0], pool), (suffixes[1], receipts), (suffixes[2], binding.read(terminal_path)),
    ):
        target = args.output.with_name(args.output.stem+suffix)
        if suffix == suffixes[0]:
            with target.open("xb") as output:
                output.write(pool_path.read_bytes())
        else:
            with target.open("x", encoding="utf-8", newline="\n") as output:
                output.write(json.dumps(data, indent=2)+"\n")
        paths.append(target)
    paths.extend((
        args.parent_audit, args.parent_digest_recheck, args.frontier, args.overlay_replay, semantic_path,
        args.narrative, args.identity_regression, args.accounting_regression,
        Path(__file__), Path(identity.__file__), Path(accounting.__file__), Path(final.__file__),
        Path(overlay.__file__), Path(__file__).with_name("test_latest_signed_full134_current_identity.py"),
        Path(__file__).with_name("test_latest_signed_full134_current_accounting.py"),
        Path(__file__).with_name("n26-latest-signed-full134rod-independent-current-accounting-proof.md"),
    ))
    distinct = {linux(Path(path)): Path(path) for path in paths}
    for text, path in distinct.items():
        digest = binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("latest old/new current inventories disagree: "+text)
        inventory[text] = digest
    print("Rehashing the ENTIRE final latest-forest current inventory.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("latest final current dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"latest_current_digests_rechecked": number, "total": len(inventory)}), flush=True)
    if binding.sha(args.parent_audit) != parent_digest or binding.read(args.frontier) != frontier:
        raise ValueError("latest final current changed its actual parent or transport partition")
    if (binding.sha(__file__) != executed_digest
            or any(binding.sha(path) != digest for path, digest in helper_digests.items())):
        raise ValueError("latest actual admission executor or its loaded helpers changed during execution")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": identity.CURRENT_SCHEMA,
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": parent_digest,
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "latest_forest_actual_published_replay_matched_and_semantics_replayed_here": True,
        "latest_forest_source_is_actual_latest_candidate_layer": True,
        "latest_forest_actual_prior_source_identity": layer,
        "latest_forest_new_whole_source_roots_lower_bounded": len(payments),
        "latest_forest_actual_full_semantic_command": command,
        "latest_forest_actual_full_semantic_exit_code": executed.returncode,
        "latest_forest_semantic_replay_file": linux(semantic_path),
        "independent_exact_latest_root_history_accounting": accounted,
        "all_newest_owned_histories_retained_identically": True,
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "actual_current_candidate_acceptance": linux(args.overlay / "VERIFIED.json"),
        "actual_current_candidate_pending_angles": linux(args.overlay / "PENDING-ANGLES.json"),
        "actual_current_candidate_remaining_history": linux(args.overlay / "REMAINING-ROOT-HISTORY.json"),
        "remaining_latest_partial_root_histories": len(retained),
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "current_frontier_actual_file": linux(args.frontier),
        "current_transport_frontier_unchanged_by_latest_partial_forests": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "candidate_transport_global_lower_bound_proved": not remaining,
        "executed_current_latest_forest_admission_file": linux(Path(__file__)),
        "executed_current_latest_forest_admission_sha256": executed_digest,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory,
    })
    with args.output.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_latest_forest_complete_current_admission_passed": True,
        "remaining_whole_roots": len(remaining), "bound_current_files": len(inventory),
        "independent_final_rehash_STILL_required": True, "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
