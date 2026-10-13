"""Fresh current-chain replay and binding of all retained competitor energy forests."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_quadratic_energy_minorant as energy
import verify_conditional_force_stage as binding
import verify_remaining_energy_forests as overlay


def main():
    parser = argparse.ArgumentParser()
    for key in ("parent-audit", "overlay", "overlay-replay", "narrative", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = binding.read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or not parent["actual_current_whole_OPEN_force_standalone_replay_matched_and_bound"]
            or parent["global_optimality_proved"] is not False):
        raise ValueError("remaining energy current extension lacks its accepted complete parent chain")
    inventory = dict(parent["files"])
    print("Rehashing the complete prior current inventory.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("remaining energy prior current dependency changed: " + text)
    accepted, paths = binding.bound(args.overlay)
    if (binding.read(args.overlay_replay) != accepted
            or accepted["source_current_audit_sha256"] != binding.sha(args.parent_audit)
            or accepted["radius_scope"] != parent["radius_scope"]
            or accepted["r_strict_interval"] != parent["r_strict_interval"]
            or not accepted["all_previously_selected_force_energy_residual_and_whole_OPEN_layers_semantically_reconstructed"]
            or binding.sha(overlay.__file__) != accepted["files"]["verify_remaining_energy_forests.py"]
            or binding.sha(energy.__file__) != accepted["files"]["n26_quadratic_energy_minorant.py"]):
        raise ValueError("remaining energy current extension lacks actual identical sealed standalone replay")
    manifest = binding.read(args.overlay / "MANIFEST.json")
    source = binding.local_path(manifest["source_overlay"])
    if (inventory.get(linux(source / "VERIFIED.json")) != accepted["source_acceptance_sha256"]
            or binding.read(source / "VERIFIED.json")["unresolved_current_competitor_closed_boxes"]
            != parent["unresolved_current_competitor_closed_boxes"]):
        raise ValueError("remaining energy current extension substituted the actual retained source roots")
    v = overlay.source_gate(args.overlay)
    print("Freshly recomputing all strict energy leaves and independent closed partitions.", flush=True)
    classes, pending, results, ledgers, frontier, removal, closed, members = overlay.derive(v)
    for name, value in (("SOURCE-LINEAGE.json", v["lineage"]), ("CLASSIFICATION.json", classes),
                        ("PENDING-TYPES.json", pending), ("FOREST-RESULTS.json", results),
                        ("LOWER-LEDGER.json", ledgers), ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                        ("CONDITIONAL-REMOVAL-LEDGER.json", removal)):
        if binding.read(args.overlay / name) != value:
            raise ValueError("remaining energy current reconstruction differs: " + name)
    if (results != accepted["accepted_closed_forests"] or closed != accepted["new_complete_type_exclusions"]
            or members != accepted["new_current_terminal_paths_removed"]
            or len(results) != accepted["all_current_retained_roots_explicitly_accounted_for_and_strictly_closed"]
            or len(v["checked"]) != accepted["all_new_positive_full_graph_kernels_and_exact_ground_inverses_checked"]
            or len(frontier["pending_states"]) != accepted["conditional_frontier_pending_subtrees"]
            or sum(len(x["closed_OPEN_boxes"]) for x in pending)
            != accepted["unresolved_current_competitor_closed_boxes"]):
        raise ValueError("remaining energy accepted current count claims did not reconstruct")
    old_pool_path = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if inventory.get(linux(old_pool_path)) != binding.sha(old_pool_path):
        raise ValueError("remaining energy closed-code pool is not the bound current parent pool")
    pool = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row for row in binding.read(old_pool_path)}
    for row in classes:
        if not row["radius_at_most_Rstar_type_excluded"]:
            continue
        code = row["spec"]["B"], tuple(row["spec"]["faces"])
        item = pool.setdefault(code, {"spec": row["spec"], "radius_scope": accepted["radius_scope"],
                                     "proof_sources": []})
        item["proof_sources"].append({
            "source": "current-all-retained-OPEN-energy-forest-overlay", "group_index": row["group_index"],
            "acceptance_sha256": binding.sha(args.overlay / "VERIFIED.json")})
    pool_path = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    if pool_path.exists():
        raise FileExistsError(pool_path)
    pool_path.write_text(json.dumps(list(pool.values()), separators=(",", ":")) + "\n", encoding="utf-8")
    paths.extend(v["inventory"])
    paths.extend([args.parent_audit, args.overlay_replay, args.narrative, pool_path,
                  Path(__file__), Path(overlay.__file__), Path(energy.__file__)])
    for path in paths:
        key, digest = linux(path), binding.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("remaining energy old/new inventories disagree: " + key)
        inventory[key] = digest
    print("Rehashing every final current dependency before publishing the audit.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("remaining energy current bytes changed during final binding")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": "N26-current-full-chain-all-retained-OPEN-energy-forest-extension-audit-v1",
        "parent_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "actual_current_remaining_energy_standalone_replay_matched_and_bound": True,
        "all_previous_selected_force_energy_and_whole_OPEN_proof_layers_freshly_reconstructed_here": True,
        "all_remaining_current_source_roots_strictly_closed_here": len(results),
        "all_new_positive_full_graph_kernels_checked_here": len(v["checked"]),
        "all_new_energy_leaf_curvature_LDL_dual_radius_and_independent_BFS_DFS_payments_recomputed_here": True,
        "explicit_older_parent_and_verified_sibling_payment_lineage_checked_here": True,
        "prior_whole_OPEN_unpaid_parents_paid_by_current_energy_forests": len(results),
        "new_complete_remaining_energy_type_exclusions": closed,
        "new_complete_current_terminal_paths_removed_by_remaining_energy_layer": members,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "current_complete_type_exclusion_indices": [row["group_index"] for row in classes
                                                    if row["radius_at_most_Rstar_type_excluded"]],
        "unresolved_current_competitor_types": accepted["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": accepted["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": accepted["conditional_frontier_pending_subtrees"],
        "Rstar_conditional_frontier_families": accepted["conditional_frontier_families"],
        "selected_catalogue_competitor_proofs_complete_not_global_enumeration": not any(
            row["closed_OPEN_boxes"] for row in pending),
        "global_catalogue_candidate_angles_and_unrestricted_reduction_still_required": True,
        "files": inventory,
    })
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
