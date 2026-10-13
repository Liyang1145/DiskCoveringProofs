"""Compose a freshly completed full-chain audit with accepted type partitions.

The old full-chain semantic replay is reused only while every bound byte still
matches. New type and conditional-partition standalone replays must actually
exist and match their acceptance reports. No historical queue is rewritten.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import local_path, sha
import verify_selected_Rstar_frontier as partition
import verify_selected_type_trees as typed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-audit", type=Path, required=True)
    parser.add_argument("--types", type=Path, required=True)
    parser.add_argument("--types-published-replay", type=Path, required=True)
    parser.add_argument("--frontier", type=Path, required=True)
    parser.add_argument("--frontier-published-replay", type=Path, required=True)
    parser.add_argument("--narrative", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["all_prior_upper_scope_and_lower_chain_replayed"]
            or not parent["same_root_entire_disk_cover_replayed"]
            or parent["local_neighbourhood_in_original_52_coordinates"] != "7/800000"
            or parent["current_pending_cover_transport_subtrees"] != 3570
            or parent["current_unresolved_terminal_subtrees"] != 10
            or parent["selected_terminal_distinct_canonical_types"] != 7
            or parent["candidate_angle_unresolved_closed_boxes"] != 103
            or parent["global_optimality_proved"]):
        raise ValueError("completed parent audit does not have the required current scope")
    inventory = {linux(local_path(text)): digest for text, digest in parent["files"].items()}
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("completed full-chain semantic replay no longer binds current bytes: " + text)
    inventory[linux(args.parent_audit)] = sha(args.parent_audit)
    types, files = bound(args.types)
    if (read(args.types_published_replay) != types or types["radius_scope"] != SCOPE
            or types["r_strict_interval"] != parent["r_strict_interval"]
            or types["original_U_frontier_nodes_removed"] != 0
            or types["Rstar_competitor_frontier_nodes_removed_by_this_bundle"] != 0
            or not types["known_candidate_positive_control"]["source_and_canonical_sharp_matrices_both_accept_candidate_tiny_box"]):
        raise ValueError("new type replay did not match its accepted root, scope and candidate")
    files.extend([args.types_published_replay])
    frontier_report, paths = bound(args.frontier)
    if (sha(partition.__file__) != frontier_report["files"]["verify_selected_Rstar_frontier.py"]
            or sha(typed.__file__) != types["files"]["verify_selected_type_trees.py"]
            or sha(partition.catalog.__file__) != frontier_report["files"]["verify_terminal_catalog.py"]):
        raise ValueError("composed audit imported arithmetic different from the sealed checkers")
    files.extend(paths)
    files.append(args.frontier_published_replay)
    if read(args.frontier_published_replay) != frontier_report:
        raise ValueError("new conditional-frontier standalone replay did not match acceptance")
    values = partition.source_gate(args.frontier)
    manifest, accepted, paths, source_report, source, table, classifications, pending, candidate, candidate_group = values
    if (accepted != types or local_path(manifest["source_types"]).resolve() != args.types.resolve()
            or source_report["families"] != parent["current_families"]
            or len(source["pending_states"]) != parent["current_pending_cover_transport_subtrees"]):
        raise ValueError("conditional partition is not connected to the replayed current original frontier")
    files.extend(paths)
    actual_frontier, ledger = partition.derive(source, table, classifications, pending, candidate)
    if (actual_frontier != read(args.frontier / "RSTAR-COMPETITOR-FRONTIER.json")
            or ledger != read(args.frontier / "CONDITIONAL-REMOVAL-LEDGER.json")
            or len(ledger) != types["strict_radius_conditional_terminal_paths_certified"]
            or len(actual_frontier["pending_states"]) != frontier_report["conditional_frontier_pending_subtrees"]):
        raise ValueError("current conditional partition or explicit removal ledger differs")
    source_orig = local_path(read(args.types / "CATALOG-SOURCE/MANIFEST.json")["source_stage"])
    for path in (source_orig / "VERIFIED.json", source_orig / "FRONTIER.json"):
        key = linux(path)
        if key not in inventory or sha(path) != inventory[key]:
            raise ValueError("original U stage was not in the unchanged full-chain binding")
    caps = local_path(read(args.types / "MANIFEST.json")["source_folders"]["caps"])
    stress = local_path(read(args.types / "MANIFEST.json")["source_folders"]["stress"])
    for path in (caps / "VERIFIED.json", stress / "VERIFIED.json"):
        key = linux(path)
        if key not in inventory or sha(path) != inventory[key]:
            raise ValueError("new radius conditions changed the parent's accepted same-root sources")
    original_error = F(read(args.types.parent / "n26-continued-leaf-candidate-angles-v1/VERIFIED.json")[
        "leaf_specific_pinning_maximum_center_error_upper"])
    if not original_error < F(8333, 10**9) < F(7, 800000):
        raise ValueError("old candidate hull entry no longer meets the unchanged local allowance")
    files.extend([Path(__file__), Path(partition.__file__), Path(typed.__file__),
                  Path(partition.catalog.__file__), args.narrative])
    for path in files:
        key, digest = linux(path), sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("new audit cannot reconcile an old and new source digest")
        inventory[key] = digest
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("current composed-audit bytes changed during the final binding")
    report = {
        "schema": "N26-current-full-chain-plus-selected-type-conditional-partition-audit-v1",
        "current_bound_bytes_rechecked": True,
        "completed_full_chain_parent_audit_sha256": sha(args.parent_audit),
        "completed_prior_full_chain_semantic_replay_preserved_and_current_hashes_rechecked": True,
        "parent_full_chain_file_digests_rechecked": len(parent["files"]),
        "new_type_exact_standalone_replay_executed_and_published_report_matched": True,
        "new_conditional_partition_standalone_replay_executed_and_report_matched": True,
        "new_conditional_partition_and_every_member_isomorphism_reconstructed_in_this_audit": True,
        "same_root_continuous_cover_and_root_interval_preserved": True,
        "r_strict_interval": parent["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "candidate_angle_unresolved_closed_boxes": 103,
        "original_U_frontier_pending_subtrees_unchanged": len(source["pending_states"]),
        "original_U_frontier_terminal_subtrees_unchanged": 10,
        "original_U_frontier_nodes_removed": 0,
        "strict_radius_conditional_selected_type_exclusions": types["strict_radius_conditional_type_exclusions"],
        "strict_radius_conditional_terminal_paths_removed": len(ledger),
        "Rstar_conditional_frontier_pending_subtrees": len(actual_frontier["pending_states"]),
        "Rstar_conditional_frontier_families": actual_frontier["families"],
        "unresolved_selected_competitor_types": types["unresolved_selected_competitor_types"],
        "unresolved_selected_competitor_closed_boxes": types["unresolved_selected_competitor_closed_boxes"],
        "all_siblings_unclosed_types_closed_boundaries_and_known_candidate_retained": True,
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "old_native_queues_and_all_frozen_bundles_unchanged": True,
        "radius_scope": SCOPE, "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
