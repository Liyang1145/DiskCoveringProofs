"""Join candidate energy payments with the full actual current enumeration."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as history
import verify_candidate_curvature_overlay as overlay
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-digest-recheck", "frontier", "overlay", "overlay-replay", "narrative", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = binding.read(args.parent_audit)
    rehash = binding.read(args.parent_digest_recheck)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or parent["radius_scope"] != binding.SCOPE or parent["global_optimality_proved"] is not False
            or rehash["current_audit_sha256"] != binding.sha(args.parent_audit)
            or not rehash["all_current_file_digests_rehashed"]
            or rehash["current_file_digests_rechecked"] != len(parent["files"])):
        raise ValueError("candidate curvature current extension lacks actual complete parent acceptance and rehash")
    inventory = dict(parent["files"])
    print("Rehashing the complete current enumeration and candidate proof chain.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("candidate current parent bytes changed: " + text)
    frontier = binding.read(args.frontier)
    if (inventory.get(linux(args.frontier)) != binding.sha(args.frontier)
            or len(frontier["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or frontier["radius_scope"] != binding.SCOPE
            or F(frontier["radius_upper"]) != F(parent["r_strict_interval"][1])):
        raise ValueError("candidate extension substituted the actual global transport frontier")
    accepted, paths = binding.bound(args.overlay)
    if (binding.read(args.overlay_replay) != accepted
            or accepted["source_actual_remaining_closed_boxes"] != parent["candidate_angle_unresolved_closed_boxes"]
            or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
            or binding.sha(overlay.__file__) != accepted["files"]["verify_candidate_curvature_overlay.py"]):
        raise ValueError("candidate current overlay lacks its actual matching executed frozen replay")
    print("Freshly reconstructing original candidate semantics and all new full-box payments.", flush=True)
    values = overlay.input_gate(args.overlay)
    manifest, original_parent, _, _, incoming, _, _, _, extra_paths = values
    paths.extend(extra_paths)
    original_parent_path = overlay.local_path(manifest["parent_current_audit"])
    if binding.sha(original_parent_path) != accepted["parent_current_audit_sha256"]:
        raise ValueError("candidate overlay changed its proof-time current audit")
    if original_parent != parent:
        # Enumeration advanced while the independent angle proof ran. It can
        # be joined only if every original dependency is identically bound in
        # the later parent and the exact angle source/root remained unchanged.
        if (inventory.get(linux(original_parent_path)) != binding.sha(original_parent_path)
                or any(inventory.get(text) != digest for text, digest in original_parent["files"].items())
                or original_parent["candidate_angle_unresolved_closed_boxes"] != len(incoming)
                or original_parent["r_strict_interval"] != parent["r_strict_interval"]
                or original_parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"):
            raise ValueError("parallel candidate proof parent is not an identical bound ancestor of the current chain")
    source_folder = overlay.local_path(manifest["source"])
    if (inventory.get(linux(source_folder / "VERIFIED.json")) != manifest["source_acceptance_sha256"]
            or inventory.get(linux(source_folder / "PENDING-ANGLES.json")) != binding.sha(
                args.overlay / "SOURCE-PENDING-ANGLES.json")):
        raise ValueError("parallel candidate proof did not use the actual unchanged current candidate angle source")
    payments, remaining = overlay.derive(values)
    positives = {**overlay.source.identity_control(values[5]), **overlay.tiny_control(values)}
    if (payments != binding.read(args.overlay / "LOWER-LEDGER.json")
            or remaining != binding.read(args.overlay / "PENDING-ANGLES.json")
            or positives != binding.read(args.overlay / "POSITIVE-CONTROLS.json")
            or len(payments) != accepted["new_strict_whole_candidate_box_energy_exclusions"]
            or len(remaining) != accepted["unresolved_closed_angle_boxes"]
            or len(payments) + len(remaining) != len(incoming)):
        raise ValueError("candidate current payments or complete retained partition did not reconstruct")
    old_pool = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if inventory.get(linux(old_pool)) != binding.sha(old_pool):
        raise ValueError("candidate extension lost the bound historical type pool")
    pool = binding.read(old_pool)
    receipts = history.retained_pool_gate(pool, parent, F(accepted["radius_upper"]))
    pool_target = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    receipt_target = args.output.with_name(args.output.stem + "-closed-receipt-checks.json")
    obligation_target = args.output.with_name(args.output.stem + "-terminal-obligations.json")
    if any(path.exists() for path in (pool_target, receipt_target, obligation_target)):
        raise FileExistsError("fresh candidate current sidecars required")
    pool_target.write_bytes(old_pool.read_bytes())
    receipt_target.write_text(json.dumps(receipts, indent=2) + "\n", encoding="utf-8")
    obligations = binding.read(args.parent_audit.with_name(args.parent_audit.stem + "-terminal-obligations.json"))
    obligation_target.write_text(json.dumps(obligations, indent=2) + "\n", encoding="utf-8")
    regression = binding.read(args.overlay / "ADAPTER-REGRESSION.json")
    test_path = Path(__file__).with_name("test_candidate_curvature_adapter.py")
    if binding.sha(test_path) != regression["executed_test_sha256"]:
        raise ValueError("candidate adapter regression runner changed")
    paths.extend([args.parent_audit, args.parent_digest_recheck, args.frontier, args.overlay_replay,
                  args.narrative, pool_target, receipt_target, obligation_target,
                  Path(__file__), Path(overlay.__file__), test_path,
                  Path(__file__).with_name("recheck_candidate_curvature_current_inventory.py"),
                  Path(__file__).with_name("n26_candidate_curvature_energy.py"),
                  Path(__file__).with_name("n26-candidate-curvature-energy-proof.md"),
                  Path(__file__).with_name("propose_candidate_curvature_energy.py"),
                  Path(__file__).with_name("n26-candidate-curvature-energy-discovery-v1.json")])
    for path in paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("old and new candidate current dependencies disagree")
        inventory[text] = digest
    if binding.read(args.frontier) != frontier:
        raise ValueError("candidate angle overlay changed the global transport frontier")
    print("Rehashing every final current dependency, historical receipt and retained box.", flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("candidate current bytes changed during final binding")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": "N26-complete-current-chain-with-original-candidate-curvature-energy-audit-v1",
        "prior_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "current_bound_bytes_rechecked": True,
        "candidate_curvature_actual_published_replay_matched_and_semantics_replayed_here": True,
        "candidate_proof_parent_is_actual_current_or_identically_bound_ancestor": True,
        "candidate_curvature_source_closed_boxes": len(incoming),
        "candidate_curvature_new_strict_whole_box_exclusions": len(payments),
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "actual_current_candidate_pending_angles": linux(args.overlay / "PENDING-ANGLES.json"),
        "actual_current_candidate_acceptance": linux(args.overlay / "VERIFIED.json"),
        "all_original_candidate_paid_nodes_closed_splits_and_unpaid_boxes_preserved": True,
        "all_original_92_rod_inverse_frame_and_new_full_box_curvature_duals_rechecked": True,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": True,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "current_global_combinatorial_frontier_nodes_removed_by_candidate_overlay": 0,
        "current_frontier_actual_file": linux(args.frontier),
        "current_transport_frontier_all_states_unchanged_by_candidate_overlay": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "candidate_curvature_negative_controls_rejected": accepted["negative_controls_rejected"],
        "candidate_transport_global_lower_bound_proved": not remaining,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory})
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
