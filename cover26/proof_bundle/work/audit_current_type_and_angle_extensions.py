"""Bind actual standalone type/angle replays without claiming a new old search."""

import argparse
from collections import Counter
import json
from pathlib import Path

from audit_prefix_partition import linux
import expanded_type_registry as registry
import verify_conditional_force_stage as stage
import verify_selected_Rstar_frontier as partition
import verify_selected_type_trees as typed


def main():
    parser = argparse.ArgumentParser()
    for key in ("parent-audit", "registry", "registry-replay", "angles",
                "angles-replay", "narrative", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = stage.read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or not parent["new_conditional_stage_actual_published_replay_matched_and_semantics_replayed_here"]
            or not parent["all_isomorphic_candidate_terminal_paths_retained"]
            or parent["global_optimality_proved"] or parent["radius_scope"] != typed.SCOPE):
        raise ValueError("type/angle extensions lack the current successive semantic chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("prior current-chain byte changed: " + text)
    inventory[linux(args.parent_audit)] = stage.sha(args.parent_audit)
    accepted, files = stage.bound(args.registry)
    if (stage.read(args.registry_replay) != accepted
            or stage.sha(registry.__file__) != accepted["files"]["expanded_type_registry.py"]):
        raise ValueError("new type registry has no matching actual sealed standalone replay")
    values = registry.input_gate(args.registry)
    manifest, pool_report, paths, cv, table, pool_rows, pool_pending, pool_domains, pool_cert, radius, caps, arcs, certificate, positive = values
    files.extend(paths)
    for key, field in (("source_catalog", "catalog_acceptance_sha256"),
                        ("source_pool", "pool_acceptance_sha256")):
        path = stage.local_path(manifest[key]) / "VERIFIED.json"
        if inventory.get(linux(path)) != manifest[field] or stage.sha(path) != manifest[field]:
            raise ValueError("new type registry source is not in the still-bound current chain")
    if (pool_report["r_strict_interval"] != parent["r_strict_interval"]
            or len(cv[3]["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or table["selected_terminal_paths"] != parent["all_current_unresolved_terminal_paths_reconstructed"]
            or table["distinct_selected_canonical_types"] != parent["current_distinct_selected_terminal_types"]
            or table["selected_candidate_type_paths"] != parent["current_candidate_type_paths"]):
        raise ValueError("type extension changed the exact root or current catalogue")
    classification = stage.read(args.registry / "CLASSIFICATION.json")
    pending = stage.read(args.registry / "PENDING-TYPES.json")
    frontier, removal = partition.derive(cv[3], table, classification, pending, cv[5])
    frontier["schema"] = "N26-expanded-canonical-type-Rstar-conditional-frontier-v1"
    frontier["source_radius_conditional_pending_subtrees"] = frontier.pop("source_original_U_pending_subtrees")
    frontier["all_nonremoved_source_conditional_states_preserved_byte_semantically"] = frontier.pop(
        "all_nonremoved_original_U_states_preserved_byte_semantically")
    frontier["radius_upper"] = str(radius)
    for row in removal:
        row["unchanged_source_radius_conditional_state"] = row.pop("unchanged_original_U_state")
    if (frontier != stage.read(args.registry / "RSTAR-COMPETITOR-FRONTIER.json")
            or removal != stage.read(args.registry / "CONDITIONAL-REMOVAL-LEDGER.json")
            or len(removal) != accepted["newly_removed_current_full_terminal_paths"]
            or len(frontier["pending_states"]) + len(removal) != len(cv[3]["pending_states"])):
        raise ValueError("new conditional type filter lost a terminal or sibling")
    candidates = [row for row in table["rows"] if row["same_canonical_type_as_known_candidate"]]
    if not all(any(state["B"] == row["B"] and state["prefix"] == row["prefix"]
                   for state in frontier["pending_states"]) for row in candidates):
        raise ValueError("an isomorphic candidate terminal was lost")
    angle_report, paths = stage.bound(args.angles)
    files.extend(paths)
    if (stage.read(args.angles_replay) != angle_report
            or angle_report["schema"] != "N26-accepted-current-candidate-angle-continuation-v1"
            or angle_report["radius_scope"] != "same-root-Rstar"
            or not angle_report["prior_all_proved_nodes_and_closed_splits_preserved"]
            or not angle_report["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]
            or angle_report["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or angle_report["executed_checker_sha256"] != angle_report["files"]["continue_current_candidate_angles.py"]):
        raise ValueError("candidate continuation lacks a sealed actual matching replay or exact root")
    angle_manifest = stage.read(args.angles / "MANIFEST.json")
    source_folder = stage.local_path(angle_manifest["sources"]["source"])
    source_path = source_folder / "VERIFIED.json"
    if (inventory.get(linux(source_path)) != angle_report["source_acceptance_sha256"]
            or stage.sha(source_path) != angle_report["source_acceptance_sha256"]):
        raise ValueError("candidate continuation source is absent from the previous current chain")
    old = stage.read(source_folder / "CERTIFICATE.json")
    tree = stage.read(args.angles / "CERTIFICATE.json")
    typed.coverage_gate(certificate["types"], table)
    if (tree["spec"] != old["spec"] or tree["radius_scope"] != "same-root-Rstar"
            or angle_report["source_OPEN_boxes"] != parent["candidate_angle_unresolved_closed_boxes"]):
        raise ValueError("candidate extension changed the source geometry or unresolved domain")
    for index, node in enumerate(old["nodes"]):
        if node["kind"] != "OPEN" and tree["nodes"][index] != node:
            raise ValueError("candidate extension changed an old paid node or split")
    counts = Counter(node["kind"] for node in tree["nodes"])
    angle_pending = stage.read(args.angles / "PENDING-ANGLES.json")
    if (any(counts[kind] != value for kind, value in angle_report["counts"].items())
            or len(angle_pending) != angle_report["unresolved_closed_angle_boxes"]
            or len(angle_pending) != counts["OPEN"]
            or stage.F(angle_report["leaf_specific_pinning_maximum_center_error_upper"]) >= stage.F(7, 800000)):
        raise ValueError("candidate extension counts or whole-hull local entry changed")
    files.extend([args.registry_replay, args.angles_replay, Path(__file__),
                  Path(registry.__file__), Path(partition.__file__), args.narrative])
    for path in files:
        key, digest = linux(path), stage.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("new and old current proof bytes disagree")
        inventory[key] = digest
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("extension bytes changed during final current binding")
    report = {
        "schema": "N26-current-successive-type-and-angle-extension-audit-v2",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": stage.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "conditional_stage_native_and_exact_actual_replays_still_bound": True,
        "new_conditional_stage_strict_whole_subtrees_excluded":
            parent["new_strict_radius_conditional_whole_subtrees_excluded"],
        "type_registry_actual_sealed_published_replay_matched_and_still_bound": True,
        "type_tree_semantics_replayed_by_sealed_checker_not_claimed_rerun_in_this_binding": True,
        "new_conditional_terminal_partition_semantically_replayed_here": True,
        "source_selected_terminal_paths": table["selected_terminal_paths"],
        "source_distinct_selected_canonical_types": table["distinct_selected_canonical_types"],
        "new_full_type_trees_exactly_replayed_by_published_checker": accepted["new_full_type_trees_exactly_replayed_here"],
        "strict_radius_conditional_current_type_exclusions": accepted["strict_radius_conditional_current_type_exclusions"],
        "new_complete_terminal_paths_removed": len(removal),
        "unresolved_current_competitor_types": accepted["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": accepted["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "current_candidate_type_paths": len(candidates),
        "all_isomorphic_candidate_terminal_paths_retained": True,
        "known_candidate_unique_complete_34_face_terminal": cv[5]["prefix"],
        "candidate_angle_actual_sealed_published_replay_matched_and_still_bound": True,
        "candidate_angle_tree_semantics_not_claimed_rerun_in_this_binding": True,
        "candidate_angle_prior_all_paid_nodes_and_closed_splits_preserved": True,
        "candidate_angle_new_strict_force_leaves": angle_report["new_strict_force_leaves"],
        "candidate_angle_new_complete_closed_splits": angle_report["new_complete_closed_splits"],
        "candidate_angle_unresolved_closed_boxes": len(angle_pending),
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": True,
        "all_siblings_unclosed_types_OPEN_boxes_and_previous_proofs_retained": True,
        "original_U_current_pending_subtrees_unchanged": parent["original_U_current_pending_subtrees_unchanged"],
        "original_U_frontier_nodes_removed_by_conditional_bundles": 0,
        "r_strict_interval": parent["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "radius_scope": typed.SCOPE,
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
