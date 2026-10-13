"""Join fresh folded-source candidate forests with the actual full current chain."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as history
import verify_current_candidate_energy_local_forests as overlay
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-digest-recheck", "frontier", "overlay",
                 "overlay-replay", "narrative", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent, rehash = binding.read(args.parent_audit), binding.read(args.parent_digest_recheck)
    if (
        not parent["current_bound_bytes_rechecked"]
        or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
        or parent["radius_scope"] != binding.SCOPE
        or parent["global_optimality_proved"] is not False
        or rehash["current_audit_sha256"] != binding.sha(args.parent_audit)
        or rehash["all_current_file_digests_rehashed"] is not True
        or rehash["current_file_digests_rechecked"] != len(parent["files"])
        or rehash["candidate_angle_unresolved_closed_boxes"] != parent["candidate_angle_unresolved_closed_boxes"]
    ):
        raise ValueError("candidate continuation join lacks the actual complete current chain and rehash")
    inventory = dict(parent["files"])
    print("Rehashing the actual current enumeration and all candidate proof dependencies.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("candidate continuation current dependency changed: " + text)
    frontier = binding.read(args.frontier)
    if (
        inventory.get(linux(args.frontier)) != binding.sha(args.frontier)
        or len(frontier["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
        or frontier["radius_scope"] != binding.SCOPE
        or F(frontier["radius_upper"]) != F(parent["r_strict_interval"][1])
    ):
        raise ValueError("candidate continuation substituted the actual combinatorial frontier")
    accepted, paths = binding.bound(args.overlay)
    if (
        binding.read(args.overlay_replay) != accepted
        or accepted["source_actual_remaining_candidate_roots"] != parent["candidate_angle_unresolved_closed_boxes"]
        or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
        or binding.sha(overlay.__file__) != accepted["files"]["verify_current_candidate_energy_local_forests.py"]
    ):
        raise ValueError("candidate continuation lacks its actual matching frozen published replay")
    print("Freshly reconstructing the folded source and every continuation closed forest.", flush=True)
    values = overlay.input_gate(args.overlay)
    manifest, proof_parent, _, original_values, incoming, proposal, extra_paths = values
    paths.extend(extra_paths)
    proof_parent_path = overlay.local_path(manifest["parent_current_audit"])
    if binding.sha(proof_parent_path) != accepted["parent_current_audit_sha256"]:
        raise ValueError("candidate continuation proof-time current parent changed")
    if proof_parent != parent:
        if (
            inventory.get(linux(proof_parent_path)) != binding.sha(proof_parent_path)
            or any(inventory.get(text) != digest for text, digest in proof_parent["files"].items())
            or proof_parent["candidate_angle_unresolved_closed_boxes"] != len(incoming)
            or proof_parent["r_strict_interval"] != parent["r_strict_interval"]
        ):
            raise ValueError("candidate continuation proof parent is not an identical bound current ancestor")
    source_folder = overlay.local_path(manifest["source"])
    if (
        inventory.get(linux(source_folder / "VERIFIED.json")) != manifest["source_acceptance_sha256"]
        or inventory.get(linux(source_folder / "PENDING-ANGLES.json")) != binding.sha(
            args.overlay / "SOURCE-PENDING-ANGLES.json"
        )
    ):
        raise ValueError("candidate continuation did not use the actual unchanged current root list")
    payments, remaining, results, boxes, ledgers = overlay.derive(values)
    positive = overlay.base.source.tiny_control(original_values)
    outputs = {
        "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": remaining,
        "ROOT-CLASSIFICATION.json": results, "PENDING-FOREST-LEAVES.json": boxes,
        "LOWER-LEDGER.json": ledgers, "POSITIVE-CONTROLS.json": positive,
    }
    if any(data != binding.read(args.overlay / name) for name, data in outputs.items()):
        raise ValueError("candidate continuation payments, retained roots or controls did not reconstruct")
    if (
        len(payments) != accepted["new_whole_candidate_source_roots_lower_bounded"]
        or len(remaining) != accepted["unresolved_closed_angle_boxes"]
        or len(payments) + len(remaining) != len(incoming)
        or any(row["source_candidate_root_strictly_empty"] and row["counts"]["LOCAL"] for row in payments)
    ):
        raise ValueError("candidate continuation lost a whole root or falsely emptied LOCAL equality")
    old_pool = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if inventory.get(linux(old_pool)) != binding.sha(old_pool):
        raise ValueError("candidate continuation lost the actual historical full-type pool")
    pool = binding.read(old_pool)
    receipts = history.retained_pool_gate(pool, parent, F(accepted["radius_upper"]))
    sidecars = {
        "-closed-type-pool.json": pool,
        "-closed-receipt-checks.json": receipts,
        "-terminal-obligations.json": binding.read(args.parent_audit.with_name(
            args.parent_audit.stem + "-terminal-obligations.json"
        )),
    }
    for suffix, data in sidecars.items():
        target = args.output.with_name(args.output.stem + suffix)
        if target.exists():
            raise FileExistsError(target)
        if suffix == "-closed-type-pool.json":
            target.write_bytes(old_pool.read_bytes())
        else:
            target.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        paths.append(target)
    paths.extend([
        args.parent_audit, args.parent_digest_recheck, args.frontier, args.overlay_replay, args.narrative,
        Path(__file__), Path(overlay.__file__), Path(overlay.current_source.__file__),
        Path(__file__).with_name("test_current_candidate_forest_source.py"),
        Path(__file__).with_name("n26-current-candidate-folded-forest-source-proof.md"),
        Path(__file__).with_name("propose_current_candidate_common_grid_forests.py"),
        Path(__file__).with_name("n26-current-candidate-common-grid-forest-discovery-v3.json"),
        Path(__file__).with_name("recheck_candidate_forest_current_inventory.py"),
    ])
    for path in paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("candidate continuation old and new current bytes disagree")
        inventory[text] = digest
    if binding.read(args.frontier) != frontier:
        raise ValueError("candidate continuation changed the actual combinatorial frontier")
    print("Rehashing every final current dependency and historical proof receipt.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("candidate continuation current bytes changed during final binding")
    report = {key: val for key, val in parent.items() if key != "files"}
    report.update({
        "schema": "N26-complete-current-chain-with-folded-candidate-forest-continuation-audit-v1",
        "current_bound_bytes_rechecked": True,
        "prior_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "candidate_forest_actual_published_replay_matched_and_semantics_replayed_here": True,
        "candidate_forest_parent_is_actual_current_or_identically_bound_ancestor": True,
        "candidate_forest_source_roots": len(incoming),
        "candidate_forest_new_whole_source_roots_lower_bounded": len(payments),
        "candidate_forest_new_strictly_empty_source_roots": accepted["new_strictly_empty_source_roots"],
        "candidate_forest_new_source_roots_discharged_using_original_LOCAL":
            accepted["new_source_roots_discharged_with_original_LOCAL"],
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "actual_current_candidate_pending_angles": linux(args.overlay / "PENDING-ANGLES.json"),
        "actual_current_candidate_acceptance": linux(args.overlay / "VERIFIED.json"),
        "all_candidate_forest_closed_halves_energy_LOCAL_leaves_and_retained_roots_rechecked": True,
        "all_original_92_rods_52_coordinate_frame_and_prior_payments_preserved": True,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": True,
        "current_global_combinatorial_frontier_nodes_removed_by_candidate_forests": 0,
        "current_frontier_actual_file": linux(args.frontier),
        "current_transport_frontier_all_states_unchanged_by_candidate_forests": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "candidate_forest_negative_controls_rejected": accepted["negative_controls_rejected"],
        "candidate_transport_global_lower_bound_proved": not remaining,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory,
    })
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
