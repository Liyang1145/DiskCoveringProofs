"""Distinct real complete-current admission of actual six-target source geometry."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_current_candidate_layer_identity as identity
import n26_six_target_current_accounting as accounting
import verify_conditional_force_stage as binding


HISTORICAL_NATIVE_FIELDS = (
    "new_conditional_stage_actual_published_replay_matched_and_semantics_replayed_here",
    "new_native_events_and_all_immediate_siblings_rechecked", "source_conditional_pending_subtrees",
    "new_stage_event_counts", "new_strict_radius_conditional_whole_subtrees_excluded",
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
    if any(path.exists() for path in [
        args.output, semantic_path, *(args.output.with_name(args.output.stem+suffix) for suffix in suffixes)
    ]):
        raise FileExistsError("six-target current never resets an existing current/final/partial target")
    parent_digest, final_digest = binding.sha(args.parent_audit), binding.sha(args.parent_final)
    parent, final = binding.read(args.parent_audit), binding.read(args.parent_final)
    if (
        final["current_audit_sha256"] != parent_digest or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(parent["files"])
        or parent["current_bound_bytes_rechecked"] is not True
        or parent["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 11183
        or parent["candidate_angle_unresolved_closed_boxes"] != 25
        or parent["global_optimality_proved"] is not False
    ):
        raise ValueError("six-target current requires the actual unchanged current28+owned8 pair; do not reset a newer head")
    manifest = binding.read(args.geometry/"MANIFEST.json")
    if (
        manifest["parent_current_sha256"] != parent_digest or manifest["parent_final_sha256"] != final_digest
        or binding.local_path(manifest["parent_current"]).resolve() != args.parent_audit.resolve()
        or binding.local_path(manifest["parent_final"]).resolve() != args.parent_final.resolve()
    ):
        raise ValueError("six-target geometry belongs to a different proof-time current pair")
    accepted = binding.read(args.geometry/"VERIFIED.json")
    checker_path = args.geometry/accounting.CHECKER
    candidate_folder = binding.local_path(manifest["actual_candidate_source"])
    layer = identity.gate(parent, parent_digest, candidate_folder)
    # Preconditions only; the real complete-current semantic main MUST run
    # below before any current report can be emitted.
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, binding.read(args.geometry_replay),
        accepted, binding.sha(checker_path), layer)
    if binding.sha(args.geometry/"VERIFIED.json") != binding.sha(args.geometry_replay):
        raise ValueError("six-target own/publication are not actually byte-identical")
    source, frontier = binding.read(args.geometry/"SOURCE-FRONTIER.json"), binding.read(args.geometry/"FRONTIER.json")
    ledger = binding.read(args.geometry/"LOWER-LEDGER.json")
    constants = binding.read(args.geometry/"FAMILY-CONSTANTS.json")
    proofs = {key: binding.sha(args.geometry/name) for key, name in {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
        "six": "SIX-CORE-TARGET-FILLED-EAR-PROOF.md",
    }.items()}
    result = accounting.partition_gate(parent, source, frontier, ledger, constants, proofs)
    regression = binding.read(args.regression)
    if (
        regression["schema"] != "N26-six-target-current-independent-accounting-controls-v1"
        or regression["verified"] is not False or regression["new_formal_geometric_payments"] != 0
        or regression["tested_accounting_sha256"] != binding.sha(accounting.__file__)
        or regression["executed_test_sha256"] != binding.sha(
            Path(__file__).with_name("test_six_target_current_accounting.py"))
        or regression["actual_parent_current_sha256"] != parent_digest
        or regression["actual_source_frontier_sha256"] != binding.sha(args.geometry/"SOURCE-FRONTIER.json")
        or regression["actual_independent_six_target_source_partition"] != result
        or regression["synthetic_receipts_NOT_actual_geometry_or_current_acceptance"] is not True
        or len(regression["actual_invalid_partition_shadow_and_witness_controls_rejected"]) != 14
        or len(regression["synthetic_invalid_geometry_receipt_controls_rejected"]) != 12
        or len(regression["synthetic_invalid_current_scope_controls_rejected"]) != 8
    ):
        raise ValueError("six-target current lacks this exact implementation's actual-source independent controls")
    executors = [
        Path(__file__), Path(__file__).with_name("recheck_six_target_source_current.py"),
        Path(__file__).with_name("test_six_target_current_accounting.py"), args.narrative, args.regression,
    ]
    work = Path(__file__).resolve().parent
    for module in list(sys.modules.values()):
        text = getattr(module, "__file__", None)
        if text:
            path = Path(text).resolve()
            if path.suffix == ".py" and path.parent == work:
                executors.append(path)
    executors = sorted({path.resolve() for path in executors})
    executor_digests = {linux(path): binding.sha(path) for path in executors}
    command = [sys.executable, str(checker_path), "--input", str(args.geometry), "--report", str(semantic_path)]
    print("Running the ENTIRE real frozen six-target main for complete-current geometry semantics.", flush=True)
    completed = subprocess.run(command, check=False)
    if completed.returncode:
        raise ValueError("actual six-target current geometry main failed; preserve partial evidence")
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, binding.read(args.geometry_replay),
        binding.read(semantic_path), binding.sha(checker_path), layer)
    if (
        binding.sha(semantic_path) != binding.sha(args.geometry/"VERIFIED.json")
        or binding.sha(args.parent_audit) != parent_digest or binding.sha(args.parent_final) != final_digest
        or binding.read(args.geometry/"MANIFEST.json") != manifest
    ):
        raise ValueError("six-target actual whole-current replay or proof-time parent changed")
    result = accounting.partition_gate(
        parent, binding.read(args.geometry/"SOURCE-FRONTIER.json"), binding.read(args.geometry/"FRONTIER.json"),
        binding.read(args.geometry/"LOWER-LEDGER.json"), binding.read(args.geometry/"FAMILY-CONSTANTS.json"), proofs)
    old_sidecars = [args.parent_audit.with_name(args.parent_audit.stem+suffix) for suffix in suffixes]
    for path in old_sidecars:
        if parent["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("six-target current lost actual historical type/receipt/raw terminal ownership")
    pool = binding.read(old_sidecars[0])
    receipts = historical.retained_pool_gate(pool, parent, F(parent["r_strict_interval"][1]))
    if receipts != binding.read(old_sidecars[1]):
        raise ValueError("six-target current changed an old proof-receipt association")
    inventory = dict(accepted["source_files"])
    paths = [args.parent_audit, args.parent_final, args.geometry/"VERIFIED.json",
             args.geometry_replay, semantic_path, *executors]
    paths.extend(args.geometry/name for name in accepted["files"])
    for suffix, original in zip(suffixes, old_sidecars):
        target = args.output.with_name(args.output.stem+suffix)
        with target.open("xb") as output:
            output.write(original.read_bytes())
        paths.append(target)
    for path in paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("six-target old/new accepted inventories disagree")
        inventory[text] = digest
    print("Rehashing every merged six-target current dependency after the complete main.", flush=True)
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("six-target merged current dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"six_target_current_inventory_rehashed": number, "total": len(inventory)}), flush=True)
    if (
        any(binding.sha(text) != digest for text, digest in executor_digests.items())
        or binding.sha(args.parent_audit) != parent_digest or binding.sha(args.parent_final) != final_digest
        or binding.read(args.geometry/"FRONTIER.json") != frontier
        or identity.gate(parent, parent_digest, candidate_folder) != layer
    ):
        raise ValueError("six-target actual executor, parent, frontier or latest source identity changed")
    report = {key: value for key, value in parent.items()
              if key != "files" and key not in HISTORICAL_NATIVE_FIELDS}
    report.update({
        "schema": accounting.CURRENT_SCHEMA, "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": parent_digest,
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "six_target_parent_audit_file": linux(args.parent_audit),
        "six_target_parent_final_file": linux(args.parent_final), "six_target_parent_final_sha256": final_digest,
        "six_target_geometry_folder": linux(args.geometry),
        "six_target_geometry_publication_file": linux(args.geometry_replay),
        "six_target_geometry_semantic_replay_file": linux(semantic_path),
        "six_target_actual_own_publication_and_current_semantic_reports_equal": True,
        "six_target_full_current_semantic_command": command, "six_target_full_current_semantic_exit_code": 0,
        "independent_exact_six_target_source_accounting": result,
        "six_target_actual_prior_candidate_layer_identity": layer,
        "candidate_layer_and_all_latest_partial_histories_unchanged_by_six_target_rule": True,
        "six_target_candidate_whole_roots_removed": 0,
        "six_target_source_conditional_pending_subtrees": len(source["pending_states"]),
        "six_target_new_strict_whole_source_prefixes": len(ledger),
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "current_frontier_actual_file": linux(args.geometry/"FRONTIER.json"),
        "inherited_native_stage28_audit_summary_NOT_six_target_events": {
            key: parent[key] for key in HISTORICAL_NATIVE_FIELDS if key in parent},
        "all_siblings_unresolved_terminals_OPEN_boundaries_and_old_proofs_retained": True,
        "six_target_current_admission_executor_file": linux(Path(__file__)),
        "six_target_current_admission_executor_sha256": executor_digests[linux(Path(__file__))],
        "six_target_independent_final_STILL_required_before_formal_head_adoption": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory,
    })
    accounting.current_gate(report, parent, result, layer)
    with args.output.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_six_target_complete_current_admission_passed": True, "proposed_current_frontier": 5637,
        "strict_whole_prefixes": 5546, "candidate_whole_roots_STILL": 25,
        "independent_final_STILL_required": True, "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
