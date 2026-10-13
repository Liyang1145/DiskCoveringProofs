"""Current full-chain composition for conditional enumeration and its catalogue."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as stage
import verify_terminal_catalog as catalog


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-audit", type=Path, required=True)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--stage-replay", type=Path, required=True)
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--catalog-replay", type=Path, required=True)
    parser.add_argument("--improved-types", type=Path)
    parser.add_argument("--improved-types-replay", type=Path)
    parser.add_argument("--type-continuation", type=Path)
    parser.add_argument("--narrative", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if any((args.improved_types, args.improved_types_replay, args.type_continuation)) and not all(
            (args.improved_types, args.improved_types_replay, args.type_continuation)):
        raise ValueError("all three optional type-improvement bindings are required together")
    parent = stage.read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or parent["Rstar_conditional_frontier_pending_subtrees"] != 3916
            or parent["original_U_current_pending_subtrees_unchanged"] != 3922
            or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or parent["global_optimality_proved"]):
        raise ValueError("conditional stage does not extend the required completed current chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("prior current-chain bytes changed: " + text)
    inventory[linux(args.parent_audit)] = stage.sha(args.parent_audit)
    accepted, files = stage.bound(args.stage)
    if (stage.read(args.stage_replay) != accepted
            or accepted["radius_scope"] != stage.SCOPE
            or stage.sha(stage.__file__) != accepted["files"]["verify_conditional_force_stage.py"]):
        raise ValueError("conditional stage standalone replay has not actually matched")
    files.extend([args.stage_replay, Path(stage.__file__)])
    area_folder = args.stage.parent / "n26-multislope-area-lower-v1"
    values = stage.input_gate(args.stage, area_folder)
    manifest, source, old_acceptance, basis, old, multi, native, trace, paths = values
    files.extend(paths)
    for field, digest_field in (("source_acceptance_original_path", "source_acceptance_sha256"),
                                ("source_frontier_original_path", "source_frontier_sha256")):
        path = stage.local_path(manifest[field])
        if inventory.get(linux(path)) != manifest[digest_field] or stage.sha(path) != manifest[digest_field]:
            raise ValueError("conditional stage source is not in the still-bound previous partition")
    if (len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or basis["r_strict_interval"] != parent["r_strict_interval"]):
        raise ValueError("conditional stage changed the previous partition size or same root")
    candidate = stage.read(args.stage / "CANDIDATE-PATH.json")
    frontier, ledger, margins = stage.replay(
        args.stage, source, old, multi, native, trace, stage.force.load_trig(args.stage)[0],
        stage.F(manifest["radius_upper"]), candidate)
    if (frontier != stage.read(args.stage / "FRONTIER.json")
            or ledger != stage.read(args.stage / "LOWER-LEDGER.json")
            or frontier["families"] != accepted["families"]):
        raise ValueError("fresh conditional stage semantic partition or ledger differs")
    for name, digest in native["files"].items():
        path = args.stage / name
        if stage.sha(path) != digest:
            raise ValueError("conditional native event evidence changed")
        files.append(path)
    cat_report, paths = stage.bound(args.catalog)
    files.extend(paths)
    files.extend([args.catalog_replay, Path(catalog.__file__)])
    if (stage.read(args.catalog_replay) != cat_report
            or stage.sha(catalog.__file__) != cat_report["files"]["verify_terminal_catalog.py"]):
        raise ValueError("new current terminal catalogue did not actually replay")
    cat_values = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *cat_values[1:])
    if (cat_values[1].resolve() != args.stage.resolve()
            or cat_values[2] != accepted or cat_values[3] != frontier
            or table != stage.read(args.catalog / "CATALOG.json")
            or table["selected_terminal_paths"] != sum(row["unresolved_terminal_subtrees"] for row in accepted["families"])
            or table["selected_candidate_type_paths"] != 1):
        raise ValueError("new terminal catalogue is not the actual current conditional terminal list")
    legacy_pending = parent["unresolved_selected_competitor_closed_boxes"]
    improved = False
    if args.improved_types:
        types, paths = stage.bound(args.improved_types)
        files.extend(paths)
        files.extend([args.improved_types_replay, args.type_continuation])
        continuation = stage.read(args.type_continuation)
        if (stage.read(args.improved_types_replay) != types
                or types["radius_scope"] != stage.SCOPE
                or types["r_strict_interval"] != accepted["r_strict_interval"]
                or types["source_acceptance_sha256"] != basis["source_acceptance_sha256"]
                or types["strict_radius_conditional_type_exclusions"] != parent["radius_conditional_types_excluded"]
                or not continuation["verified"]
                or not continuation["all_prior_non_OPEN_nodes_and_closed_splits_unchanged"]
                or continuation["old_acceptance_sha256"] != manifest["radius_basis_acceptance_sha256"]
                or continuation["new_acceptance_sha256"] != stage.sha(args.improved_types / "VERIFIED.json")):
            raise ValueError("optional old-type refinement changed radius or claims unapplied type exclusions")
        for text, digest in continuation["files"].items():
            if stage.sha(text) != digest:
                raise ValueError("type-refinement paid-node preservation bytes changed")
            key = linux(stage.local_path(text))
            if key in inventory and inventory[key] != digest:
                raise ValueError("type refinement disagrees with old current-chain bytes")
            inventory[key] = digest
        legacy_pending = types["unresolved_selected_competitor_closed_boxes"]
        improved = True
    old_type_codes = {(row["spec"]["B"], tuple(row["spec"]["faces"]))
                      for row in stage.read(stage.local_path(manifest["radius_basis"]) / "CLASSIFICATION.json")}
    new_types = [i for i, group in enumerate(table["groups"])
                 if not any(table["rows"][j]["same_canonical_type_as_known_candidate"] for j in group["member_indices"])
                 and (group["B"], tuple(group["canonical_faces"])) not in old_type_codes]
    files.extend([Path(__file__), args.narrative])
    for path in files:
        key, digest = linux(path), stage.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("old and new current binding inventories disagree")
        inventory[key] = digest
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("conditional stage current bytes changed during final binding")
    report = {
        "schema": "N26-current-full-chain-conditional-enumeration-and-terminal-catalogue-audit-v1",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": stage.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "new_conditional_stage_actual_standalone_replay_matched_and_semantics_replayed_in_this_audit": True,
        "new_native_events_and_all_immediate_siblings_rechecked": native["native_events_checked"],
        "new_stage_event_counts": accepted["event_counts"],
        "new_strict_radius_conditional_whole_subtrees_excluded": accepted["new_strict_radius_conditional_whole_transport_subtrees_excluded"],
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "all_current_unresolved_terminal_paths_reconstructed": table["selected_terminal_paths"],
        "current_distinct_selected_terminal_types": table["distinct_selected_canonical_types"],
        "current_candidate_type_paths": 1,
        "current_new_competitor_type_indices_without_preexisting_accepted_trees": new_types,
        "old_selected_type_refinement_actual_replay_and_paid_node_preservation_bound": improved,
        "old_selected_competitor_types_still_pending": parent["unresolved_selected_competitor_types"],
        "old_selected_competitor_closed_boxes_still_pending": legacy_pending,
        "new_current_catalogue_actual_published_replay_and_every_bijection_reconstructed": True,
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "all_siblings_unresolved_terminals_OPEN_boundaries_and_old_proofs_retained": True,
        "original_U_current_pending_subtrees_unchanged": parent["original_U_current_pending_subtrees_unchanged"],
        "original_U_frontier_nodes_removed_by_conditional_bundle": 0,
        "r_strict_interval": accepted["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "candidate_angle_unresolved_closed_boxes": parent["candidate_angle_unresolved_closed_boxes"],
        "radius_scope": stage.SCOPE, "screen_radius_threshold": str(stage.force.U),
        "inherited_source_is_unconditional_at_U": False,
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
