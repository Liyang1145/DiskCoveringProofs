"""Bind current conditional enumeration with seven new complete type exclusions."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import expanded_type_registry as registry
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-audit", type=Path, required=True)
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--registry-replay", type=Path, required=True)
    parser.add_argument("--narrative", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or parent["Rstar_conditional_frontier_pending_subtrees"] != 4223
            or parent["all_current_unresolved_terminal_paths_reconstructed"] != 12
            or parent["current_distinct_selected_terminal_types"] != 11
            or parent["old_selected_competitor_closed_boxes_still_pending"] != 16
            or not parent["old_selected_type_refinement_actual_replay_and_paid_node_preservation_bound"]
            or parent["global_optimality_proved"]):
        raise ValueError("expanded registry lacks the required current source-stage chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if sha(text) != digest:
            raise ValueError("completed conditional current chain has changed bytes")
    inventory[linux(args.parent_audit)] = sha(args.parent_audit)
    accepted, files = bound(args.registry)
    if (read(args.registry_replay) != accepted
            or sha(registry.__file__) != accepted["files"]["expanded_type_registry.py"]):
        raise ValueError("expanded registry actual standalone replay did not match acceptance")
    values = registry.input_gate(args.registry)
    manifest, pool_report, paths, cv, table, pool_rows, pool_pending, pool_domains, pool_cert, radius, caps, arcs, certificate, positive = values
    files.extend(paths)
    for key, digest_field in (("source_catalog", "catalog_acceptance_sha256"),
                              ("source_pool", "pool_acceptance_sha256")):
        path = local_path(manifest[key]) / "VERIFIED.json"
        if inventory.get(linux(path)) != manifest[digest_field] or sha(path) != manifest[digest_field]:
            raise ValueError("expanded registry source catalogue or proof pool is not in the bound current chain")
    if (pool_report["r_strict_interval"] != parent["r_strict_interval"]
            or len(cv[3]["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or table["selected_terminal_paths"] != parent["all_current_unresolved_terminal_paths_reconstructed"]
            or table["distinct_selected_canonical_types"] != parent["current_distinct_selected_terminal_types"]):
        raise ValueError("expanded registry changed the current root or selected terminal scope")
    result = registry.derive(table, pool_report, pool_rows, pool_pending, pool_domains, pool_cert,
                             certificate, radius, caps, arcs, cv[3], cv[5])
    classification, pending, ledger, domains, reused, frontier, removal = result
    for name, value in (("CLASSIFICATION.json", classification), ("PENDING-TYPES.json", pending),
                        ("LOWER-LEDGER.json", ledger), ("DOMAINS.json", domains), ("REUSED-TYPES.json", reused),
                        ("RSTAR-COMPETITOR-FRONTIER.json", frontier), ("CONDITIONAL-REMOVAL-LEDGER.json", removal),
                        ("CANDIDATE-POSITIVE-CONTROL.json", positive)):
        if read(args.registry / name) != value:
            raise ValueError("expanded registry actual closed tree, proof reuse or current partition differs")
    if (len(removal) != accepted["newly_removed_current_full_terminal_paths"]
            or frontier["families"] != accepted["conditional_frontier_families"]
            or len(frontier["pending_states"]) + len(removal) != len(cv[3]["pending_states"])
            or accepted["unresolved_current_competitor_closed_boxes"] != parent["old_selected_competitor_closed_boxes_still_pending"]):
        raise ValueError("expanded conditional partition lost a terminal, sibling or retained OPEN box")
    files.extend([args.registry_replay, Path(__file__), Path(registry.__file__), args.narrative])
    for path in files:
        key, digest = linux(path), sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("earlier and expanded current chain disagree on shared proof bytes")
        inventory[key] = digest
    for text, digest in inventory.items():
        if sha(text) != digest:
            raise ValueError("expanded current-chain bytes changed during final binding")
    report = {
        "schema": "N26-current-full-chain-conditional-stage-and-expanded-type-registry-audit-v1",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "conditional_stage_native_and_exact_published_replays_still_bound": True,
        "new_conditional_stage_strict_whole_subtrees_excluded": parent["new_strict_radius_conditional_whole_subtrees_excluded"],
        "expanded_registry_actual_published_replay_matched_and_all_new_tree_semantics_replayed_here": True,
        "source_selected_terminal_paths": table["selected_terminal_paths"],
        "source_distinct_selected_canonical_types": table["distinct_selected_canonical_types"],
        "new_full_type_trees_exactly_replayed_here": accepted["new_full_type_trees_exactly_replayed_here"],
        "new_full_type_exclusion_indices": accepted["strict_radius_conditional_current_type_exclusions"],
        "new_complete_terminal_paths_removed": len(removal),
        "prior_complete_type_proofs_reused_only_with_identical_full_spec_root_and_matrix": len(reused),
        "unresolved_current_competitor_types": accepted["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": accepted["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "known_candidate_unique_complete_34_face_terminal": cv[5]["prefix"],
        "all_siblings_unclosed_types_OPEN_boxes_and_previous_proofs_retained": True,
        "same_root_cover_and_candidate_exact_tiny_box_positive_control_replayed": True,
        "original_U_current_pending_subtrees_unchanged": parent["original_U_current_pending_subtrees_unchanged"],
        "original_U_frontier_nodes_removed_by_conditional_bundles": 0,
        "r_strict_interval": parent["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "candidate_angle_unresolved_closed_boxes": parent["candidate_angle_unresolved_closed_boxes"],
        "radius_scope": accepted["radius_scope"],
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
