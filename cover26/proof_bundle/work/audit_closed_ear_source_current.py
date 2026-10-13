"""Distinct complete-current admission of real closed-ear source geometry.

No cached DATA report substitutes for running the frozen geometry main.
The independent final is required before the new current becomes formal head.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_closed_ear_current_accounting as accounting
import n26_current_candidate_layer_identity as identity
import verify_conditional_force_stage as binding


HISTORICAL_NATIVE_FIELDS = (
    "new_conditional_stage_actual_published_replay_matched_and_semantics_replayed_here",
    "new_native_events_and_all_immediate_siblings_rechecked",
    "source_conditional_pending_subtrees", "new_stage_event_counts",
    "new_strict_radius_conditional_whole_subtrees_excluded",
    "frontier_conservation_per_family_independently_checked",
)


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-final", "geometry", "geometry-replay",
                 "regression", "narrative", "output"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    semantic_path = args.output.with_name(args.output.stem+"-geometry-semantic-replay.json")
    suffixes = ("-closed-type-pool.json", "-closed-receipt-checks.json", "-terminal-obligations.json")
    targets = [args.output, semantic_path,
               *(args.output.with_name(args.output.stem+suffix) for suffix in suffixes)]
    if any(path.exists() for path in targets):
        raise FileExistsError("closed-ear current needs fresh targets; never repeat a finished main")
    parent_digest, final_digest = binding.sha(args.parent_audit), binding.sha(args.parent_final)
    parent, parent_final = binding.read(args.parent_audit), binding.read(args.parent_final)
    if (
        parent_final["current_audit_sha256"] != parent_digest
        or parent_final["all_current_file_digests_rehashed"] is not True
        or parent_final["current_file_digests_rechecked"] != len(parent["files"])
        or parent["current_bound_bytes_rechecked"] is not True
        or parent["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 11183
        or parent["candidate_angle_unresolved_closed_boxes"] != 25
        or parent["global_optimality_proved"] is not False
    ):
        raise ValueError("closed-ear current lacks the actual completed unchanged parent pair")
    manifest = binding.read(args.geometry/"MANIFEST.json")
    checker_path = args.geometry/accounting.CHECKER
    accepted = binding.read(args.geometry/"VERIFIED.json")
    candidate_folder = binding.local_path(manifest["actual_candidate_source"])
    layer = identity.gate(parent, parent_digest, candidate_folder)
    if (
        manifest["parent_current_sha256"] != parent_digest
        or manifest["parent_final_sha256"] != final_digest
        or binding.local_path(manifest["parent_current"]).resolve() != args.parent_audit.resolve()
        or binding.local_path(manifest["parent_final"]).resolve() != args.parent_final.resolve()
    ):
        raise ValueError("closed-ear geometry was prepared for a different current/final pair")
    # This first call is a prerequisite check only. The real semantic main
    # below must subsequently succeed and match before any current is written.
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, binding.read(args.geometry_replay),
        accepted, binding.sha(checker_path), layer)
    if binding.sha(args.geometry/"VERIFIED.json") != binding.sha(args.geometry_replay):
        raise ValueError("actual same-main geometry publication is not byte-identical")
    source = binding.read(args.geometry/"SOURCE-FRONTIER.json")
    frontier = binding.read(args.geometry/"FRONTIER.json")
    ledger = binding.read(args.geometry/"LOWER-LEDGER.json")
    constants = binding.read(args.geometry/"FAMILY-CONSTANTS.json")
    proofs = {key: binding.sha(args.geometry/name) for key, name in {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
    }.items()}
    result = accounting.partition_gate(parent, source, frontier, ledger, constants, proofs)
    regression = binding.read(args.regression)
    if (
        regression["schema"] != "N26-closed-ear-current-independent-accounting-controls-v1"
        or regression["tested_accounting_sha256"] != binding.sha(accounting.__file__)
        or regression["executed_test_sha256"] != binding.sha(
            Path(__file__).with_name("test_closed_ear_current_accounting.py"))
        or regression["actual_parent_current_sha256"] != parent_digest
        or regression["actual_source_frontier_sha256"] != binding.sha(args.geometry/"SOURCE-FRONTIER.json")
        or regression["actual_independent_source_partition"] != result
        or regression["synthetic_receipts_NOT_actual_geometry_or_current_acceptance"] is not True
        or regression["actual_own_geometry_and_current_main_NOT_executed_by_controls"] is not True
        or regression["verified"] is not False or regression["new_geometric_payments"] != 0
        or len(regression["actual_invalid_source_case_and_partition_controls_rejected"]) != 14
        or len(regression["synthetic_invalid_receipt_and_scope_controls_rejected"]) != 12
        or len(regression["synthetic_invalid_current_scope_controls_rejected"]) != 8
    ):
        raise ValueError("closed-ear current lacks actual-source independent accounting controls")
    executors = [
        Path(__file__), Path(accounting.__file__), Path(identity.__file__),
        Path(historical.__file__), Path(binding.__file__),
        Path(__file__).with_name("recheck_closed_ear_source_current.py"),
        Path(__file__).with_name("test_closed_ear_current_accounting.py"),
        args.regression, args.narrative,
    ]
    work_folder = Path(__file__).resolve().parent
    for module in list(sys.modules.values()):
        module_file = getattr(module, "__file__", None)
        if module_file:
            path = Path(module_file).resolve()
            if path.suffix == ".py" and path.parent == work_folder:
                executors.append(path)
    executors = sorted(set(path.resolve() for path in executors))
    executor_digests = {linux(path): binding.sha(path) for path in executors}
    command = [sys.executable, str(checker_path), "--input", str(args.geometry),
               "--report", str(semantic_path)]
    print("Executing the ENTIRE frozen ear geometry main for actual complete-current semantics.", flush=True)
    completed = subprocess.run(command, check=False)
    if completed.returncode:
        raise ValueError("closed-ear whole geometry main failed; preserve all partial evidence")
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, binding.read(args.geometry_replay),
        binding.read(semantic_path), binding.sha(checker_path), layer)
    if (
        binding.sha(semantic_path) != binding.sha(args.geometry/"VERIFIED.json")
        or binding.sha(args.parent_audit) != parent_digest
        or binding.sha(args.parent_final) != final_digest
        or binding.read(args.geometry/"MANIFEST.json") != manifest
    ):
        raise ValueError("ear current actual semantic replay or frozen parent changed")
    result = accounting.partition_gate(
        parent, binding.read(args.geometry/"SOURCE-FRONTIER.json"),
        binding.read(args.geometry/"FRONTIER.json"), binding.read(args.geometry/"LOWER-LEDGER.json"),
        binding.read(args.geometry/"FAMILY-CONSTANTS.json"), proofs)
    pool_path = args.parent_audit.with_name(args.parent_audit.stem+suffixes[0])
    receipts_path = args.parent_audit.with_name(args.parent_audit.stem+suffixes[1])
    terminal_path = args.parent_audit.with_name(args.parent_audit.stem+suffixes[2])
    for path in (pool_path, receipts_path, terminal_path):
        if parent["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("ear current lost a bound historical pool/receipt/terminal sidecar")
    pool = binding.read(pool_path)
    receipts = historical.retained_pool_gate(pool, parent, F(parent["r_strict_interval"][1]))
    if receipts != binding.read(receipts_path):
        raise ValueError("ear current changed an old proof-receipt association")
    inventory = dict(accepted["source_files"])
    paths = [args.parent_audit, args.parent_final, args.geometry/"VERIFIED.json",
             args.geometry_replay, semantic_path, *executors]
    paths.extend(args.geometry/name for name in accepted["files"])
    for suffix, source_path in zip(suffixes, (pool_path, receipts_path, terminal_path)):
        target = args.output.with_name(args.output.stem+suffix)
        with target.open("xb") as output:
            output.write(source_path.read_bytes())
        paths.append(target)
    for path in paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("ear old/new dependency inventories disagree")
        inventory[text] = digest
    print("Rehashing every merged current dependency after source semantics and historical retention.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("closed-ear merged current dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"closed_ear_current_inventory_rehashed": number,
                              "total": len(inventory)}), flush=True)
    if (
        any(binding.sha(text) != digest for text, digest in executor_digests.items())
        or binding.sha(args.parent_audit) != parent_digest
        or binding.sha(args.parent_final) != final_digest
        or binding.read(args.geometry/"FRONTIER.json") != frontier
        or identity.gate(parent, parent_digest, candidate_folder) != layer
    ):
        raise ValueError("ear actual executor, parent, frontier or latest candidate layer changed")
    report = {key: value for key, value in parent.items()
              if key != "files" and key not in HISTORICAL_NATIVE_FIELDS}
    report.update({
        "schema": accounting.CURRENT_SCHEMA,
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": parent_digest,
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "closed_ear_parent_audit_file": linux(args.parent_audit),
        "closed_ear_parent_final_file": linux(args.parent_final),
        "closed_ear_parent_final_sha256": final_digest,
        "closed_ear_geometry_folder": linux(args.geometry),
        "closed_ear_geometry_publication_file": linux(args.geometry_replay),
        "closed_ear_actual_published_and_complete_current_semantic_replays_equal": True,
        "closed_ear_full_current_semantic_command": command,
        "closed_ear_full_current_semantic_exit_code": completed.returncode,
        "closed_ear_geometry_semantic_replay_file": linux(semantic_path),
        "independent_exact_closed_ear_source_accounting": result,
        "closed_ear_actual_prior_candidate_layer_identity": layer,
        "candidate_layer_and_all_latest_partial_histories_unchanged_by_closed_ear": True,
        "closed_ear_candidate_whole_roots_removed": 0,
        "closed_ear_source_conditional_pending_subtrees": len(source["pending_states"]),
        "closed_ear_new_strict_whole_source_prefixes": len(ledger),
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "current_frontier_actual_file": linux(args.geometry/"FRONTIER.json"),
        "inherited_native_stage28_audit_summary_NOT_new_ear_events": {
            key: parent[key] for key in HISTORICAL_NATIVE_FIELDS if key in parent},
        "all_siblings_unresolved_terminals_OPEN_boundaries_and_old_proofs_retained": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "closed_ear_current_admission_executor_file": linux(Path(__file__)),
        "closed_ear_current_admission_executor_sha256": executor_digests[linux(Path(__file__))],
        "closed_ear_independent_final_STILL_required_before_formal_head_adoption": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory,
    })
    accounting.current_gate(report, parent, result, layer)
    with args.output.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_complete_closed_ear_current_admission_passed": True,
        "proposed_current_frontier": len(frontier["pending_states"]),
        "strict_whole_prefixes": len(ledger), "candidate_whole_roots_STILL": 25,
        "independent_final_STILL_required": True, "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
