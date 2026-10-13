"""Current binding of a successive conditional stage and all terminal types."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as stage
import verify_terminal_catalog as catalog


def main():
    parser = argparse.ArgumentParser()
    for key in ("parent-audit", "stage", "stage-replay", "catalog",
                "catalog-replay", "narrative", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = stage.read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or parent["original_U_current_pending_subtrees_unchanged"] != 3922
            or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or parent["radius_scope"] != stage.SCOPE or parent["global_optimality_proved"]):
        raise ValueError("successive stage lacks an accepted current conditional parent chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("prior current chain changed: " + text)
    inventory[linux(args.parent_audit)] = stage.sha(args.parent_audit)
    accepted, files = stage.bound(args.stage)
    if (stage.read(args.stage_replay) != accepted
            or accepted["radius_scope"] != stage.SCOPE
            or stage.sha(stage.__file__) != accepted["files"]["verify_conditional_force_stage.py"]):
        raise ValueError("successive conditional stage has no matching actual published replay")
    values = stage.input_gate(args.stage, args.stage.parent / "n26-multislope-area-lower-v1")
    manifest, source, old_acceptance, basis, old, multi, native, trace, paths = values
    files.extend(paths)
    for field, digest_field in (("source_acceptance_original_path", "source_acceptance_sha256"),
                                ("source_frontier_original_path", "source_frontier_sha256")):
        path = stage.local_path(manifest[field])
        if inventory.get(linux(path)) != manifest[digest_field] or stage.sha(path) != manifest[digest_field]:
            raise ValueError("successive source is not the parent's still-bound current partition")
    if (len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or basis["r_strict_interval"] != parent["r_strict_interval"]
            or accepted["source_conditional_pending_subtrees"] != len(source["pending_states"])):
        raise ValueError("successive stage changed the prior frontier or exact covering root")
    candidate = stage.read(args.stage / "CANDIDATE-PATH.json")
    frontier, ledger, margins = stage.replay(
        args.stage, source, old, multi, native, trace, stage.force.load_trig(args.stage)[0],
        stage.F(manifest["radius_upper"]), candidate)
    if (frontier != stage.read(args.stage / "FRONTIER.json")
            or ledger != stage.read(args.stage / "LOWER-LEDGER.json")
            or frontier["families"] != accepted["families"]):
        raise ValueError("successive conditional stage semantic partition differs")
    for name, digest in native["files"].items():
        path = args.stage / name
        if stage.sha(path) != digest:
            raise ValueError("native successor sibling evidence changed")
        files.append(path)
    cat_report, paths = stage.bound(args.catalog)
    files.extend(paths)
    if (stage.read(args.catalog_replay) != cat_report
            or stage.sha(catalog.__file__) != cat_report["files"]["verify_terminal_catalog.py"]):
        raise ValueError("current terminal catalogue lacks its actual published replay")
    cv = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *cv[1:])
    if (cv[1].resolve() != args.stage.resolve() or cv[2] != accepted or cv[3] != frontier
            or table != stage.read(args.catalog / "CATALOG.json")
            or table["selected_terminal_paths"] != sum(row["unresolved_terminal_subtrees"]
                                                        for row in accepted["families"])):
        raise ValueError("catalogue omitted or substituted a current terminal")
    candidate_members = [i for i, row in enumerate(table["rows"])
                         if row["same_canonical_type_as_known_candidate"]]
    candidate_groups = [i for i, group in enumerate(table["groups"])
                        if any(j in candidate_members for j in group["member_indices"])]
    if (not candidate_members or len(candidate_groups) != 1
            or len(candidate_members) != table["selected_candidate_type_paths"]
            or not any(table["rows"][i]["prefix"] == candidate["prefix"] for i in candidate_members)):
        raise ValueError("known candidate or an isomorphic terminal path was lost")
    prior_registry = stage.local_path(manifest["source_acceptance_original_path"]).parent
    prior_rows = stage.read(prior_registry / "CLASSIFICATION.json")
    prior_codes = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row for row in prior_rows}
    reused_codes, fresh_codes = [], []
    for index, group in enumerate(table["groups"]):
        if index in candidate_groups:
            continue
        key = (group["B"], tuple(group["canonical_faces"]))
        if key in prior_codes:
            reused_codes.append({"current_group_index": index,
                                 "prior_group_index": prior_codes[key]["group_index"],
                                 "prior_type_excluded": prior_codes[key]["radius_at_most_Rstar_type_excluded"]})
        else:
            fresh_codes.append(index)
    files.extend([args.stage_replay, args.catalog_replay, Path(stage.__file__),
                  Path(catalog.__file__), Path(__file__), args.narrative])
    for path in files:
        key, digest = linux(path), stage.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("successive and prior inventories disagree")
        inventory[key] = digest
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("current conditional bytes changed during final binding")
    report = {
        "schema": "N26-current-successive-conditional-stage-and-terminal-catalogue-audit-v2",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": stage.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "new_conditional_stage_actual_published_replay_matched_and_semantics_replayed_here": True,
        "new_native_events_and_all_immediate_siblings_rechecked": native["native_events_checked"],
        "source_conditional_pending_subtrees": len(source["pending_states"]),
        "new_stage_event_counts": accepted["event_counts"],
        "new_strict_radius_conditional_whole_subtrees_excluded":
            accepted["new_strict_radius_conditional_whole_transport_subtrees_excluded"],
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "all_current_unresolved_terminal_paths_reconstructed": table["selected_terminal_paths"],
        "current_distinct_selected_terminal_types": table["distinct_selected_canonical_types"],
        "current_candidate_type_paths": len(candidate_members),
        "all_isomorphic_candidate_terminal_paths_retained": True,
        "candidate_canonical_group_index": candidate_groups[0],
        "current_types_matching_prior_registry_by_full_spec": reused_codes,
        "current_new_competitor_type_indices_without_prior_registry_trees": fresh_codes,
        "old_selected_competitor_types_still_pending": parent["unresolved_current_competitor_types"],
        "old_selected_competitor_closed_boxes_still_pending": parent["unresolved_current_competitor_closed_boxes"],
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
        "global_optimality_proved": False, "n27_started": False, "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
