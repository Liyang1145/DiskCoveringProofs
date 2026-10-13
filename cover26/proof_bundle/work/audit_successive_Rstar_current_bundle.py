"""Bind a later original-U stage and its explicit conditional type transfer."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import local_path, sha
import verify_successive_Rstar_frontier as transfer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-audit", type=Path, required=True)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--stage-replay", type=Path, required=True)
    parser.add_argument("--conditional", type=Path, required=True)
    parser.add_argument("--conditional-replay", type=Path, required=True)
    parser.add_argument("--narrative", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["completed_prior_full_chain_semantic_replay_preserved_and_current_hashes_rechecked"]
            or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or parent["original_U_frontier_pending_subtrees_unchanged"] != 3570
            or parent["global_optimality_proved"]):
        raise ValueError("earlier current full-chain binding has a wrong scope")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("prior full-chain bound bytes changed: " + text)
    inventory[linux(args.parent_audit)] = sha(args.parent_audit)
    stage, files = bound(args.stage)
    if (read(args.stage_replay) != stage
            or not stage["all_incoming_angle_boxes_covered"]
            or not stage["older_forests_and_original_native_queues_preserved"]):
        raise ValueError("later-stage exact published replay is not accepted")
    files.append(args.stage_replay)
    manifest = read(args.stage / "MANIFEST.json")
    for field, digest_field in (("source_frontier_original_path", "source_frontier_sha256"),
                                ("source_acceptance_original_path", "source_acceptance_sha256")):
        source = local_path(manifest[field])
        if inventory.get(linux(source)) != manifest[digest_field] or sha(source) != manifest[digest_field]:
            raise ValueError("new U stage is not a complete continuation of the bound old U frontier")
    native = read(args.stage / "NATIVE-VERIFIED.json")
    for name, digest in native["files"].items():
        path = args.stage / name
        if sha(path) != digest:
            raise ValueError("new native sibling/event evidence changed")
        files.append(path)
    conditional, paths = bound(args.conditional)
    files.extend(paths)
    files.append(args.conditional_replay)
    if (read(args.conditional_replay) != conditional
            or conditional["source_acceptance_sha256"]["stage"] != sha(args.stage / "VERIFIED.json")
            or sha(transfer.__file__) != conditional["files"]["verify_successive_Rstar_frontier.py"]):
        raise ValueError("new conditional partition replay or executed checker changed")
    values = transfer.input_gate(args.conditional)
    cm, reports, paths, original, table, classifications, pending, candidate, candidate_group = values
    files.extend(paths)
    types_folder = local_path(cm["source_folders"]["types"])
    if (reports["stage"] != stage
            or inventory.get(linux(types_folder / "VERIFIED.json")) != sha(types_folder / "VERIFIED.json")
            or reports["types"]["r_strict_interval"] != parent["r_strict_interval"]
            or original != read(args.stage / "FRONTIER.json")
            or len(original["pending_states"]) != stage["pending_cover_transport_subtrees"]):
        raise ValueError("new stage and conditional geometry are not in the unchanged root/source chain")
    actual, ledger, members = transfer.derive(original, table, classifications, pending, candidate)
    if (actual != read(args.conditional / "RSTAR-COMPETITOR-FRONTIER.json")
            or ledger != read(args.conditional / "CONDITIONAL-REMOVAL-LEDGER.json")
            or members != read(args.conditional / "COMPLETE-MEMBER-TRANSFER.json")
            or len(ledger) != reports["types"]["strict_radius_conditional_terminal_paths_certified"]
            or actual["families"] != conditional["conditional_frontier_families"]):
        raise ValueError("new current conditional ownership or canonical-member ledger differs")
    files.extend([Path(__file__), Path(transfer.__file__), args.narrative])
    for path in files:
        key, digest = linux(path), sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("old and new current bindings disagree")
        inventory[key] = digest
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("current successive-stage bytes changed during final binding")
    report = {
        "schema": "N26-current-full-chain-successive-U-stage-and-Rstar-type-transfer-audit-v1",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "new_stage_actual_exact_standalone_acceptance_and_published_replay_matched": True,
        "new_stage_native_events_and_all_siblings_bound": native["native_events_checked"],
        "new_stage_event_counts": stage["event_counts"],
        "new_stage_strict_whole_transport_subtrees_excluded": stage["strictly_excluded_whole_transport_subtrees"],
        "new_stage_all_incoming_angle_boxes_covered": True,
        "original_U_current_families": stage["families"],
        "original_U_current_pending_subtrees": len(original["pending_states"]),
        "original_U_current_terminal_subtrees": sum(row["unresolved_terminal_subtrees"] for row in stage["families"]),
        "new_conditional_partition_actual_standalone_replay_matched": True,
        "all_selected_complete_members_and_explicit_bijections_reconstructed_on_new_stage": len(members),
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "radius_conditional_types_excluded": reports["types"]["strict_radius_conditional_type_exclusions"],
        "radius_conditional_terminal_paths_removed": len(ledger),
        "Rstar_conditional_frontier_pending_subtrees": len(actual["pending_states"]),
        "Rstar_conditional_frontier_families": actual["families"],
        "all_siblings_unclosed_types_OPEN_boxes_and_candidate_retained": True,
        "r_strict_interval": parent["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "candidate_angle_unresolved_closed_boxes": parent["candidate_angle_unresolved_closed_boxes"],
        "unresolved_selected_competitor_types": reports["types"]["unresolved_selected_competitor_types"],
        "unresolved_selected_competitor_closed_boxes": reports["types"]["unresolved_selected_competitor_closed_boxes"],
        "radius_scope": SCOPE, "original_U_frontier_nodes_removed_by_conditional_filters": 0,
        "all_old_queues_frozen_bundles_and_earlier_current_audits_unchanged": True,
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
