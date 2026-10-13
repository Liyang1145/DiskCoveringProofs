"""Fresh full-current binding and exact replay of the whole-OPEN force extension."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_correlated_arc_force as force
import verify_conditional_force_stage as binding
import verify_current_force_open_overlay as overlay


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
            or not parent["actual_current_hybrid_standalone_replay_matched_and_bound"]
            or parent["global_optimality_proved"] is not False):
        raise ValueError("whole-OPEN current audit lacks the accepted complete parent chain")
    inventory = dict(parent["files"])
    print("Rehashing the complete prior current inventory.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("prior full-current dependency changed: " + text)
    accepted, paths = binding.bound(args.overlay)
    if (binding.read(args.overlay_replay) != accepted
            or accepted["source_current_audit_sha256"] != binding.sha(args.parent_audit)
            or accepted["radius_scope"] != parent["radius_scope"]
            or accepted["r_strict_interval"] != parent["r_strict_interval"]
            or not accepted["all_previously_selected_force_energy_and_residual_layers_semantically_reconstructed"]
            or binding.sha(overlay.__file__) != accepted["files"]["verify_current_force_open_overlay.py"]
            or binding.sha(force.__file__) != accepted["files"]["n26_correlated_arc_force.py"]):
        raise ValueError("whole-OPEN current audit lacks an actual identical sealed standalone replay")
    manifest = binding.read(args.overlay / "MANIFEST.json")
    source = binding.local_path(manifest["source_overlay"])
    source_accepted = binding.read(source / "VERIFIED.json")
    if (inventory.get(linux(source / "VERIFIED.json")) != accepted["source_acceptance_sha256"]
            or source_accepted["unresolved_current_competitor_closed_boxes"]
            != parent["unresolved_current_competitor_closed_boxes"]
            or source_accepted["conditional_frontier_pending_subtrees"]
            != parent["Rstar_conditional_frontier_pending_subtrees"]):
        raise ValueError("whole-OPEN overlay substituted the actual current pending partition")
    v = overlay.source_gate(args.overlay)
    print("Freshly recomputing all whole-OPEN flow bounds and exact terminal transfer.", flush=True)
    classes, pending, payments, unpaid = overlay.derive(
        v["classes"], v["pending"], v["domains"], v["certificate"], v["radius"], v["arcs"])
    frontier, removal, newly_closed, member_count = overlay.transfer(v, classes, pending)
    for name, value in (("SOURCE-LINEAGE.json", v["lineage"]), ("SOURCE-TREE-REPLAYS.json", v["replayed"]),
                        ("CLASSIFICATION.json", classes), ("PENDING-TYPES.json", pending),
                        ("LOWER-LEDGER.json", payments), ("UNPAID-CHECKS.json", unpaid),
                        ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                        ("CONDITIONAL-REMOVAL-LEDGER.json", removal)):
        if binding.read(args.overlay / name) != value:
            raise ValueError("fresh whole-OPEN current reconstruction differs: " + name)
    if (len(payments) != accepted["new_strict_whole_current_OPEN_force_payments"]
            or len(unpaid) != accepted["unpaid_whole_source_OPEN_checks_retained"]
            or newly_closed != accepted["new_complete_type_exclusions"]
            or member_count != accepted["new_current_terminal_paths_removed"]
            or len(frontier["pending_states"]) != accepted["conditional_frontier_pending_subtrees"]
            or sum(len(x["closed_OPEN_boxes"]) for x in pending)
            != accepted["unresolved_current_competitor_closed_boxes"]):
        raise ValueError("whole-OPEN accepted count claims did not independently reconstruct")
    old_pool_path = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if inventory.get(linux(old_pool_path)) != binding.sha(old_pool_path):
        raise ValueError("whole-OPEN closed code pool is not the bound actual current pool")
    pool = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row for row in binding.read(old_pool_path)}
    for row in classes:
        if not row["radius_at_most_Rstar_type_excluded"]:
            continue
        code = row["spec"]["B"], tuple(row["spec"]["faces"])
        item = pool.setdefault(code, {"spec": row["spec"], "radius_scope": accepted["radius_scope"],
                                     "proof_sources": []})
        item["proof_sources"].append({
            "source": "current-whole-OPEN-correlated-force-overlay", "group_index": row["group_index"],
            "acceptance_sha256": binding.sha(args.overlay / "VERIFIED.json")})
    pool_path = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    if pool_path.exists():
        raise FileExistsError(pool_path)
    pool_path.write_text(json.dumps(list(pool.values()), separators=(",", ":")) + "\n", encoding="utf-8")
    paths.extend(v["inventory"])
    paths.extend([args.parent_audit, args.overlay_replay, args.narrative, pool_path,
                  Path(__file__), Path(overlay.__file__), Path(force.__file__)])
    for path in paths:
        key, digest = linux(path), binding.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("prior and whole-OPEN inventories disagree: " + key)
        inventory[key] = digest
    print("Rehashing every final current dependency before publishing the audit.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("whole-OPEN current bytes changed during final binding")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": "N26-current-full-chain-whole-OPEN-correlated-force-extension-audit-v1",
        "parent_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "actual_current_whole_OPEN_force_standalone_replay_matched_and_bound": True,
        "all_previous_selected_energy_force_residual_layers_freshly_reconstructed_here": True,
        "new_selected_source_full_force_tree_nodes_replayed_here": sum(row["nodes"] for row in v["replayed"]),
        "new_selected_source_force_trees_complete_BFS_DFS_partitions_and_old_ledgers_matched_here": True,
        "explicit_older_discovery_to_current_complete_records_and_exact_matrices_checked_here": True,
        "whole_OPEN_new_strict_payments": len(payments),
        "whole_OPEN_unpaid_source_records_retained": len(unpaid),
        "new_complete_whole_OPEN_force_type_exclusions": newly_closed,
        "new_complete_current_terminal_paths_removed_by_whole_OPEN_force_layer": member_count,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "current_complete_type_exclusion_indices": [row["group_index"] for row in classes
                                                    if row["radius_at_most_Rstar_type_excluded"]],
        "unresolved_current_competitor_types": accepted["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": accepted["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": accepted["conditional_frontier_pending_subtrees"],
        "Rstar_conditional_frontier_families": accepted["conditional_frontier_families"],
        "all_unpaid_unvisited_closed_source_boxes_candidate_paths_and_prior_proofs_retained": True,
        "files": inventory,
    })
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
