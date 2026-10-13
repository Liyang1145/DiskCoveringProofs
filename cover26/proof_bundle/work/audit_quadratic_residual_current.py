"""Bind the residual-forest extension and freshly replay its complete halves."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_quadratic_box_forest as forest
import n26_quadratic_energy_minorant as energy
import verify_conditional_force_stage as binding
import verify_quadratic_residual_overlay as residual
import verify_quadratic_type_overlay as previous


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
            or not parent["actual_current_quadratic_standalone_replay_matched_and_bound"]
            or parent["global_optimality_proved"]):
        raise ValueError("residual current extension lacks the accepted joined proof chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("joined current dependency changed: " + text)
    accepted, files = binding.bound(args.overlay)
    if (binding.read(args.overlay_replay) != accepted
            or accepted["radius_scope"] != parent["radius_scope"]
            or accepted["r_strict_interval"] != parent["r_strict_interval"]
            or not accepted["source_overlay_full_force_and_prior_energy_layers_semantically_replayed"]
            or binding.sha(forest.__file__) != accepted["files"]["n26_quadratic_box_forest.py"]
            or binding.sha(residual.__file__) != accepted["files"]["verify_quadratic_residual_overlay.py"]
            or binding.sha(energy.__file__) != accepted["files"]["n26_quadratic_energy_minorant.py"]):
        raise ValueError("residual extension lacks actual matching sealed replay")
    manifest = binding.read(args.overlay / "MANIFEST.json")
    source = binding.local_path(manifest["source_overlay"])
    source_acceptance = source / "VERIFIED.json"
    if (inventory.get(linux(source_acceptance)) != accepted["source_acceptance_sha256"]
            or binding.read(source_acceptance)["unresolved_current_competitor_closed_boxes"]
            != parent["unresolved_current_competitor_closed_boxes"]):
        raise ValueError("residual extension is not based on the current joined pending boxes")
    source_manifest = binding.read(source / "MANIFEST.json")
    base = binding.local_path(source_manifest["source_registry"])
    domains = binding.read(base / "DOMAINS.json")
    old_class = binding.read(source / "CLASSIFICATION.json")
    old_pending = binding.read(source / "PENDING-TYPES.json")
    kernels = binding.read(args.overlay / "KERNELS.json")
    checked = [energy.kernel_gate(row["certificate"]["spec"], row["certificate"]) for row in kernels]
    certificate = binding.read(args.overlay / "FORESTS.json")
    radius = F(accepted["radius_upper"])
    arcs = previous.typed.force.load_trig(args.overlay)[0]
    classification, pending, results, ledgers = residual.derive(
        old_class, old_pending, domains, certificate, checked, radius, arcs)
    if (classification != binding.read(args.overlay / "CLASSIFICATION.json")
            or pending != binding.read(args.overlay / "PENDING-TYPES.json")
            or results != binding.read(args.overlay / "FOREST-RESULTS.json")
            or ledgers != binding.read(args.overlay / "LOWER-LEDGER.json")
            or results != accepted["selected_residual_forests"]):
        raise ValueError("fresh independent forest replay differs from published layer")
    source_table = binding.read(base / "SOURCE-CATALOG.json")
    original_frontier = binding.read(base / "SOURCE-CONDITIONAL-FRONTIER.json")
    base_manifest = binding.read(base / "MANIFEST.json")
    catalog_folder = binding.local_path(base_manifest["source_catalog"])
    candidate = binding.read(catalog_folder / "CANDIDATE-PATH.json")
    frontier, removal = previous.frontier(original_frontier, source_table, classification, pending, candidate, radius)
    if (frontier != binding.read(args.overlay / "RSTAR-COMPETITOR-FRONTIER.json")
            or removal != binding.read(args.overlay / "CONDITIONAL-REMOVAL-LEDGER.json")
            or len(frontier["pending_states"]) != accepted["conditional_frontier_pending_subtrees"]):
        raise ValueError("residual current canonical terminal partition changed")
    old_pool_path = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    old_pool = binding.read(old_pool_path)
    pool = {(row["spec"]["B"], tuple(row["spec"]["faces"])): row for row in old_pool}
    for row in classification:
        if not row["radius_at_most_Rstar_type_excluded"]:
            continue
        key = row["spec"]["B"], tuple(row["spec"]["faces"])
        item = pool.setdefault(key, {"spec": row["spec"], "radius_scope": accepted["radius_scope"],
                                    "proof_sources": []})
        item["proof_sources"].append({"source": "current-quadratic-residual-forest-overlay",
                                      "group_index": row["group_index"],
                                      "acceptance_sha256": binding.sha(args.overlay / "VERIFIED.json")})
    pool_path = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    if pool_path.exists():
        raise FileExistsError(pool_path)
    pool_path.write_text(json.dumps(list(pool.values()), separators=(",", ":")) + "\n", encoding="utf-8")
    files.extend([args.parent_audit, args.overlay_replay, Path(__file__), Path(forest.__file__),
                  Path(residual.__file__), Path(energy.__file__), args.narrative, pool_path])
    for path in files:
        key, digest = linux(path), binding.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("old and residual current inventories disagree")
        inventory[key] = digest
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("residual current bytes changed during final binding")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": "N26-current-full-chain-quadratic-residual-forest-extension-audit-v1",
        "parent_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "actual_current_residual_standalone_replay_matched_and_bound": True,
        "all_new_closed_halves_BFS_DFS_bounds_and_strict_energy_payments_recomputed_here": True,
        "new_complete_residual_type_exclusions": accepted["new_complete_type_exclusions"],
        "new_complete_current_terminal_paths_removed_by_residual_layer": accepted["new_current_terminal_paths_removed"],
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "current_complete_type_exclusion_indices": [row["group_index"] for row in classification
                                                    if row["radius_at_most_Rstar_type_excluded"]],
        "unresolved_current_competitor_types": accepted["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": accepted["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": accepted["conditional_frontier_pending_subtrees"],
        "Rstar_conditional_frontier_families": accepted["conditional_frontier_families"],
        "all_unselected_exploratory_forests_remain_unaccepted_and_source_parents_retained": True,
        "files": inventory})
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
