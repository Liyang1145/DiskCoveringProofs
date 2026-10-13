"""Fresh current-chain audit of the additive hybrid closure and actual terminal transfer."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_hybrid_box_forest as forest
import n26_quadratic_energy_minorant as energy
import verify_conditional_force_stage as binding
import verify_last_hard_hybrid_overlay as overlay
import verify_quadratic_type_overlay as quadratic


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
            or not parent["actual_current_residual_standalone_replay_matched_and_bound"]
            or parent["global_optimality_proved"]):
        raise ValueError("hybrid current extension lacks the accepted residual current chain")
    inventory = dict(parent["files"])
    print("Rehashing the complete parent current inventory.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("prior current dependency changed: " + text)
    accepted, paths = binding.bound(args.overlay)
    if (binding.read(args.overlay_replay) != accepted
            or accepted["radius_scope"] != parent["radius_scope"]
            or accepted["r_strict_interval"] != parent["r_strict_interval"]
            or not accepted["source_full_force_and_prior_energy_and_residual_layers_semantically_replayed"]
            or binding.sha(forest.__file__) != accepted["files"]["n26_hybrid_box_forest.py"]
            or binding.sha(overlay.__file__) != accepted["files"]["verify_last_hard_hybrid_overlay.py"]
            or binding.sha(energy.__file__) != accepted["files"]["n26_quadratic_energy_minorant.py"]):
        raise ValueError("hybrid current overlay lacks actual matching sealed standalone replay")
    manifest = binding.read(args.overlay / "MANIFEST.json")
    source = binding.local_path(manifest["source_overlay"])
    source_accepted = binding.read(source / "VERIFIED.json")
    if (inventory.get(linux(source / "VERIFIED.json")) != accepted["source_acceptance_sha256"]
            or source_accepted["unresolved_current_competitor_closed_boxes"]
            != parent["unresolved_current_competitor_closed_boxes"]
            or source_accepted["conditional_frontier_pending_subtrees"]
            != parent["Rstar_conditional_frontier_pending_subtrees"]):
        raise ValueError("hybrid is not based on the actual current unresolved partition")
    print("Reconstructing previous layers, explicit lineage and all new integer kernels.", flush=True)
    v = overlay.source_gate(args.overlay)
    if v["classes"] != binding.read(source / "CLASSIFICATION.json"):
        raise ValueError("hybrid source classification did not freshly reconstruct")
    print("Freshly recomputing every hybrid energy/force leaf and canonical transfer.", flush=True)
    classes, pending, results, ledgers = overlay.derive(
        v["classes"], v["pending"], v["domains"], v["certificate"],
        v["checked"], v["radius"], v["arcs"])
    frontier, removal = quadratic.frontier(v["cv"][3], v["table"], classes, pending, v["cv"][5], v["radius"])
    for name, value in (("SOURCE-LINEAGE.json", v["lineage"]), ("CLASSIFICATION.json", classes),
                        ("PENDING-TYPES.json", pending), ("FOREST-RESULTS.json", results),
                        ("LOWER-LEDGER.json", ledgers), ("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                        ("CONDITIONAL-REMOVAL-LEDGER.json", removal)):
        if binding.read(args.overlay / name) != value:
            raise ValueError("fresh hybrid current arithmetic differs: " + name)
    if (results != accepted["selected_hybrid_forests"]
            or len(frontier["pending_states"]) != accepted["conditional_frontier_pending_subtrees"]
            or sum(len(x["closed_OPEN_boxes"]) for x in pending)
            != accepted["unresolved_current_competitor_closed_boxes"]):
        raise ValueError("hybrid acceptance count claims did not freshly reconstruct")
    key = lambda row: (row["B"], tuple(row["prefix"]))
    old_states = {key(x): x for x in v["frontier"]["pending_states"]}
    new_states = {key(x): x for x in frontier["pending_states"]}
    old_paid, new_paid = {key(x): x for x in v["removal"]}, {key(x): x for x in removal}
    newly_closed = sorted({x["group_index"] for x in classes if x["radius_at_most_Rstar_type_excluded"]}
                          - {x["group_index"] for x in v["classes"] if x["radius_at_most_Rstar_type_excluded"]})
    actual_members = {key(member) for x in v["classes"] if x["group_index"] in newly_closed
                      for member in x["members"]}
    if (not set(new_states) <= set(old_states) or not set(old_paid) <= set(new_paid)
            or any(new_states[k] != old_states[k] for k in new_states)
            or any(new_paid[k] != old_paid[k] for k in old_paid)
            or set(old_states) - set(new_states) != set(new_paid) - set(old_paid)
            or set(old_states) - set(new_states) != actual_members
            or newly_closed != accepted["new_complete_type_exclusions"]
            or len(actual_members) != accepted["new_current_terminal_paths_removed"]):
        raise ValueError("hybrid current terminal closure does not preserve exact ownership")
    for row in v["table"]["rows"]:
        if row["same_canonical_type_as_known_candidate"] and key(row) not in new_states:
            raise ValueError("hybrid current transfer lost a candidate isomorphic path")
    old_pool_path = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if inventory.get(linux(old_pool_path)) != binding.sha(old_pool_path):
        raise ValueError("hybrid closed-code pool is not the actual bound parent pool")
    pool = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row for row in binding.read(old_pool_path)}
    for row in classes:
        if not row["radius_at_most_Rstar_type_excluded"]:
            continue
        code = row["spec"]["B"], tuple(row["spec"]["faces"])
        item = pool.setdefault(code, {"spec": row["spec"], "radius_scope": accepted["radius_scope"],
                                     "proof_sources": []})
        item["proof_sources"].append({
            "source": "current-additive-positive-kernel-hybrid-overlay",
            "group_index": row["group_index"],
            "acceptance_sha256": binding.sha(args.overlay / "VERIFIED.json")})
    pool_path = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    if pool_path.exists():
        raise FileExistsError(pool_path)
    pool_path.write_text(json.dumps(list(pool.values()), separators=(",", ":")) + "\n", encoding="utf-8")
    paths.extend(v["inventory"])
    paths.extend([args.parent_audit, args.overlay_replay, Path(__file__), Path(forest.__file__),
                  Path(overlay.__file__), Path(energy.__file__), args.narrative, pool_path])
    for path in paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("old and hybrid current inventories disagree: " + text)
        inventory[text] = digest
    print("Rehashing every final current dependency before publishing the audit.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("hybrid current bytes changed during final binding: " + text)
    report = {k: value for k, value in parent.items() if k != "files"}
    report.update({
        "schema": "N26-current-full-chain-last-hard-additive-hybrid-extension-audit-v1",
        "parent_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "actual_current_hybrid_standalone_replay_matched_and_bound": True,
        "all_prior_selected_force_energy_and_residual_layers_freshly_reconstructed_here": True,
        "explicit_older_discovery_to_current_identical_OPEN_lineage_freshly_checked_here": True,
        "all_new_positive_integer_kernels_checked_here": len(v["checked"]),
        "all_new_closed_halves_BFS_DFS_strict_energy_and_force_payments_recomputed_here": True,
        "new_complete_hybrid_type_exclusions": newly_closed,
        "new_complete_current_terminal_paths_removed_by_hybrid_layer": len(actual_members),
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "current_complete_type_exclusion_indices": [row["group_index"] for row in classes
                                                    if row["radius_at_most_Rstar_type_excluded"]],
        "unresolved_current_competitor_types": accepted["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": accepted["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": accepted["conditional_frontier_pending_subtrees"],
        "Rstar_conditional_frontier_families": accepted["conditional_frontier_families"],
        "old_three_difficult_types_unresolved_closed_boxes": {
            str(i): len(next(row for row in pending if row["group_index"] == i)["closed_OPEN_boxes"])
            for i in (36, 37, 38)},
        "unused_discovery_kernels_verified_but_never_counted_as_leaf_payments": True,
        "all_other_exploratory_forests_remain_unaccepted_and_prior_evidence_retained": True,
        "files": inventory,
    })
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: value for k, value in report.items() if k != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
