"""Compose accepted partial-force forests with the intact full current chain."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_sharp_partial_forest as partial
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-audit", type=Path, required=True)
    parser.add_argument("--forest", type=Path, required=True)
    parser.add_argument("--forest-replay", type=Path, required=True)
    parser.add_argument("--positive-controls", type=Path, required=True)
    parser.add_argument("--narrative", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or parent["original_U_current_pending_subtrees"] != 3922
            or parent["Rstar_conditional_frontier_pending_subtrees"] != 3917
            or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or parent["global_optimality_proved"]):
        raise ValueError("sharp partial audit has a wrong previous complete chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("prior completed current chain no longer binds its exact bytes")
    inventory[linux(args.parent_audit)] = sha(args.parent_audit)
    forest, files = bound(args.forest)
    if (read(args.forest_replay) != forest
            or sha(partial.__file__) != forest["files"]["verify_sharp_partial_forest.py"]):
        raise ValueError("partial forest has no current matching actual standalone replay")
    files.append(args.forest_replay)
    positive = read(args.positive_controls)
    if (not positive["verified"] or not positive["same_root_cover_and_exact_tiny_angle_containment_replayed"]
            or not positive["all_35_partial_domains_include_known_exact_cover"]
            or positive["all_candidate_prefix_states_checked"] != 35
            or positive["radius_upper"] != forest["radius_upper"]
            or not positive["all_completed_domain_bounds_imply_partial_bounds"]):
        raise ValueError("partial-domain independent candidate controls did not actually pass")
    for text, digest in positive["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("partial positive-control source bytes changed")
        if text in inventory and inventory[text] != digest:
            raise ValueError("partial positive controls are not on the current exact root")
        inventory[text] = digest
    files.append(args.positive_controls)
    values = partial.input_gate(args.forest)
    manifest, reports, paths, original, baseline, candidate, radius, caps, arcs, certificate = values
    files.extend(paths)
    baseline_folder = local_path(manifest["source_conditional_frontier"])
    if (inventory.get(linux(baseline_folder / "VERIFIED.json")) != manifest["source_conditional_acceptance_sha256"]
            or len(original["pending_states"]) != parent["original_U_current_pending_subtrees"]
            or len(baseline["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or reports["types"]["r_strict_interval"] != parent["r_strict_interval"]):
        raise ValueError("partial forest changed the current original or conditional frontier")
    frontier, results, pending, ledger, domains = partial.derive(
        original, baseline, candidate, radius, caps, arcs, certificate["roots"])
    for name, value in (("RSTAR-COMPETITOR-FRONTIER.json", frontier), ("CLASSIFICATION.json", results),
                        ("PENDING-PARTIAL-ANGLES.json", pending), ("LOWER-LEDGER.json", ledger), ("DOMAINS.json", domains)):
        if read(args.forest / name) != value:
            raise ValueError("current partial tree, exact leaf ledger or whole-node partition differs")
    if (frontier["families"] != forest["conditional_frontier_families"]
            or frontier["new_sharp_partial_whole_subtrees_excluded"]
            != forest["new_strict_radius_conditional_whole_partial_subtrees_excluded"]):
        raise ValueError("current partial payments are not the accepted payments")
    files.extend([Path(__file__), Path(partial.__file__), Path(partial.independent.__file__), args.narrative])
    for path in files:
        key, digest = linux(path), sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("old and new partial current bindings disagree")
        inventory[key] = digest
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("sharp partial current bytes changed during final content binding")
    report = {
        "schema": "N26-current-full-chain-with-sharp-partial-subtree-forest-audit-v1",
        "current_bound_bytes_rechecked": True, "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "new_partial_forest_actual_standalone_acceptance_and_published_replay_matched": True,
        "all_new_partial_domains_closed_trees_exact_ledgers_and_partitions_reconstructed_in_this_audit": True,
        "all_35_candidate_partial_domains_exact_root_positive_controls_replayed_and_bound": True,
        "new_radius_conditional_whole_partial_subtrees_excluded": frontier["new_sharp_partial_whole_subtrees_excluded"],
        "new_partial_trees_checked": len(results),
        "unresolved_attempted_partial_roots_retained": forest["retained_attempted_partial_roots"],
        "unresolved_attempted_partial_closed_boxes_retained": forest["retained_attempted_partial_closed_OPEN_boxes"],
        "original_U_current_pending_subtrees_unchanged": len(original["pending_states"]),
        "original_U_frontier_nodes_removed_by_conditional_filters": 0,
        "radius_conditional_full_type_terminal_paths_removed": parent["radius_conditional_terminal_paths_removed"],
        "radius_conditional_types_excluded": parent["radius_conditional_types_excluded"],
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "all_siblings_unclosed_types_shared_boundaries_and_unvisited_nodes_retained": True,
        "r_strict_interval": parent["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "candidate_angle_unresolved_closed_boxes": parent["candidate_angle_unresolved_closed_boxes"],
        "unresolved_selected_competitor_types": parent["unresolved_selected_competitor_types"],
        "unresolved_selected_competitor_closed_boxes": parent["unresolved_selected_competitor_closed_boxes"],
        "radius_scope": forest["radius_scope"],
        "all_old_queues_frozen_bundles_and_earlier_current_audits_unchanged": True,
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
