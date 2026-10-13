"""Join the primary and third-stage chains with actual current energy payments."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import expanded_type_registry as registry
import n26_quadratic_energy_minorant as energy
import verify_conditional_force_stage as binding
import verify_quadratic_type_overlay as quadratic
import verify_registry_catalogue_transfer as transport


def merge_inventory(inventory, additions):
    for text, digest in additions.items():
        key = linux(binding.local_path(text))
        if binding.sha(text) != digest:
            raise ValueError("joined current dependency changed: " + text)
        if key in inventory and inventory[key] != digest:
            raise ValueError("joined current chains disagree on shared bytes")
        inventory[key] = digest


def main():
    parser = argparse.ArgumentParser()
    for key in ("primary-audit", "branch-audit", "old-registry", "registry", "registry-replay",
                "type-transfer", "old-overlay", "old-overlay-replay",
                "overlay", "overlay-replay", "narrative", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    primary, branch = binding.read(args.primary_audit), binding.read(args.branch_audit)
    for parent in (primary, branch):
        if (not parent["current_bound_bytes_rechecked"]
                or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
                or parent["global_optimality_proved"]
                or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"):
            raise ValueError("joined current proof lacks an accepted unchanged parent chain")
    if (primary["r_strict_interval"] != branch["r_strict_interval"]
            or primary["candidate_angle_unresolved_closed_boxes"] != branch["candidate_angle_unresolved_closed_boxes"]
            or not branch["new_conditional_stage_actual_published_replay_matched_and_semantics_replayed_here"]):
        raise ValueError("joined branches changed the exact root or candidate scope")
    inventory = {}
    merge_inventory(inventory, primary["files"])
    merge_inventory(inventory, branch["files"])
    current, files = binding.bound(args.registry)
    old, paths = binding.bound(args.old_registry)
    files.extend(paths)
    transfer = binding.read(args.type_transfer)
    if (binding.read(args.registry_replay) != current or not transfer["verified"]
            or transfer["old_acceptance_sha256"] != binding.sha(args.old_registry / "VERIFIED.json")
            or transfer["new_acceptance_sha256"] != binding.sha(args.registry / "VERIFIED.json")
            or inventory.get(linux(args.old_registry / "VERIFIED.json")) != transfer["old_acceptance_sha256"]
            or current["r_strict_interval"] != primary["r_strict_interval"]):
        raise ValueError("joined current registry has no matched actual replay or accepted canonical transfer")
    fresh_transfer = transport.transfer(args.old_registry, args.registry)
    if any(transfer[key] != value for key, value in fresh_transfer.items()):
        raise ValueError("joined canonical proof preservation did not freshly reconstruct")
    merge_inventory(inventory, transfer["files"])
    values = registry.input_gate(args.registry)
    manifest, pool_report, paths, cv, table, pool_rows, pool_pending, pool_domains, pool_cert, radius, caps, arcs, certificate, positive = values
    files.extend(paths)
    catalog_path = binding.local_path(manifest["source_catalog"]) / "VERIFIED.json"
    if (inventory.get(linux(catalog_path)) != current["catalog_acceptance_sha256"]
            or len(cv[3]["pending_states"]) != branch["Rstar_conditional_frontier_pending_subtrees"]
            or table["selected_terminal_paths"] != branch["all_current_unresolved_terminal_paths_reconstructed"]
            or table["distinct_selected_canonical_types"] != branch["current_distinct_selected_terminal_types"]):
        raise ValueError("current registry was not built on the actual third-stage branch")
    old_energy, paths = binding.bound(args.old_overlay)
    files.extend(paths)
    new_energy, paths = binding.bound(args.overlay)
    files.extend(paths)
    if (binding.read(args.old_overlay_replay) != old_energy
            or binding.read(args.overlay_replay) != new_energy
            or old_energy["source_acceptance_sha256"] != binding.sha(args.old_registry / "VERIFIED.json")
            or new_energy["source_acceptance_sha256"] != binding.sha(args.registry / "VERIFIED.json")
            or old_energy["radius_upper"] != new_energy["radius_upper"]
            or F(new_energy["radius_upper"]) != radius
            or binding.sha(energy.__file__) != new_energy["files"]["n26_quadratic_energy_minorant.py"]
            or binding.sha(quadratic.__file__) != new_energy["files"]["verify_quadratic_type_overlay.py"]):
        raise ValueError("quadratic overlays lack identical-root actual sealed standalone replays")
    classification = binding.read(args.registry / "CLASSIFICATION.json")
    pending = binding.read(args.registry / "PENDING-TYPES.json")
    domains = binding.read(args.registry / "DOMAINS.json")
    proposal = binding.read(args.overlay / "PROPOSAL.json")
    kernels = binding.read(args.overlay / "KERNELS.json")
    checked = [energy.kernel_gate(row["certificate"]["spec"], row["certificate"]) for row in kernels]
    new_class, new_pending, payments, unpaid = quadratic.derive(
        classification, pending, domains, proposal, kernels, checked, radius, arcs)
    frontier, removal = quadratic.frontier(cv[3], table, new_class, new_pending, cv[5], radius)
    for name, value in (("CLASSIFICATION.json", new_class), ("PENDING-TYPES.json", new_pending),
                        ("LOWER-LEDGER.json", payments), ("UNPAID-CHECKS.json", unpaid),
                        ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                        ("CONDITIONAL-REMOVAL-LEDGER.json", removal)):
        if binding.read(args.overlay / name) != value:
            raise ValueError("current exact energy payments or terminal filter did not reconstruct")
    old_payments = binding.read(args.old_overlay / "LOWER-LEDGER.json")
    by_old = {(row["spec"]["B"], tuple(row["spec"]["faces"]), row["source_closed_OPEN_box"]["index"]): row
              for row in old_payments}
    by_new = {(row["spec"]["B"], tuple(row["spec"]["faces"]), row["source_closed_OPEN_box"]["index"]): row
              for row in payments}
    if set(by_old) != set(by_new) or any(
            {key: value for key, value in by_old[k].items() if key != "group_index"}
            != {key: value for key, value in by_new[k].items() if key != "group_index"} for k in by_old):
        raise ValueError("old accepted energy payment changed during full-spec catalogue transfer")
    closed_pool = {}
    for label, folder, rows in (("prior-catalogue-quadratic-overlay", args.old_overlay,
                                 binding.read(args.old_overlay / "CLASSIFICATION.json")),
                                ("current-catalogue-quadratic-overlay", args.overlay, new_class)):
        for row in rows:
            if not row["radius_at_most_Rstar_type_excluded"]:
                continue
            key = row["spec"]["B"], tuple(row["spec"]["faces"])
            item = closed_pool.setdefault(key, {"spec": row["spec"], "radius_scope": current["radius_scope"],
                                                "proof_sources": []})
            item["proof_sources"].append({"source": label, "group_index": row["group_index"],
                                          "acceptance_sha256": binding.sha(folder / "VERIFIED.json")})
    pool_path = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    if pool_path.exists():
        raise FileExistsError(pool_path)
    pool_path.write_text(json.dumps(list(closed_pool.values()), separators=(",", ":")) + "\n", encoding="utf-8")
    files.extend([args.primary_audit, args.branch_audit, args.registry_replay, args.type_transfer,
                  args.old_overlay_replay, args.overlay_replay, Path(__file__), Path(transport.__file__),
                  Path(quadratic.__file__), Path(energy.__file__), args.narrative, pool_path])
    for path in files:
        merge_inventory(inventory, {linux(path): binding.sha(path)})
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("joined current bytes changed during final binding")
    report = {
        "schema": "N26-current-full-chain-joined-catalogue-and-quadratic-energy-audit-v1",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "primary_parent_audit_sha256": binding.sha(args.primary_audit),
        "third_stage_parent_audit_sha256": binding.sha(args.branch_audit),
        "primary_parent_file_digests_rechecked": len(primary["files"]),
        "third_stage_parent_file_digests_rechecked": len(branch["files"]),
        "native_and_exact_third_stage_published_replays_still_bound": True,
        "new_conditional_stage_strict_whole_subtrees_excluded": branch["new_strict_radius_conditional_whole_subtrees_excluded"],
        "complete_code_type_transfer_and_all_old_paid_nodes_freshly_recomputed": True,
        "old_full_types_matched_by_full_spec": len(fresh_transfer["matched_full_types"]),
        "old_closed_full_type_proofs_retained_for_absent_current_types":
            len(fresh_transfer["absent_old_closed_type_proofs_still_bound"]),
        "fresh_current_full_type_roots": len(fresh_transfer["fresh_new_full_type_roots"]),
        "old_non_OPEN_nodes_preserved_across_catalogues": fresh_transfer["previous_non_OPEN_nodes_preserved"],
        "actual_current_quadratic_standalone_replay_matched_and_bound": True,
        "all_current_integer_inverse_LDL_dual_and_radius_square_payments_recomputed_here": True,
        "old_accepted_energy_payments_transferred_only_with_identical_complete_graph_and_SOURCE_OPEN": len(payments),
        "joined_closed_full_type_codes_in_these_two_catalogues": len(closed_pool),
        "all_earlier_other_type_proofs_remain_bound_not_counted_in_this_union": True,
        "current_distinct_selected_terminal_types": table["distinct_selected_canonical_types"],
        "current_selected_terminal_paths_before_type_filter": table["selected_terminal_paths"],
        "current_complete_type_exclusion_indices": [row["group_index"] for row in new_class
                                                    if row["radius_at_most_Rstar_type_excluded"]],
        "new_quadratic_complete_current_type_exclusions": new_energy["new_complete_full_type_exclusions"],
        "unresolved_current_competitor_types": new_energy["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": new_energy["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "current_candidate_type_paths": table["selected_candidate_type_paths"],
        "all_isomorphic_candidate_terminal_paths_retained": True,
        "known_candidate_unique_complete_34_face_terminal": cv[5]["prefix"],
        "candidate_Dirichlet_actual_sealed_published_replay_still_bound": True,
        "candidate_Dirichlet_new_strict_whole_box_exclusions": primary["candidate_Dirichlet_new_strict_whole_box_exclusions"],
        "candidate_angle_unresolved_closed_boxes": primary["candidate_angle_unresolved_closed_boxes"],
        "all_siblings_unclosed_types_OPEN_boxes_and_previous_proofs_retained": True,
        "original_U_current_pending_subtrees_unchanged": primary["original_U_current_pending_subtrees_unchanged"],
        "original_U_frontier_nodes_removed_by_conditional_bundles": 0,
        "r_strict_interval": primary["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "radius_scope": current["radius_scope"],
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
