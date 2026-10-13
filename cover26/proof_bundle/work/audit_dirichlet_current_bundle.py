"""Bind and freshly recompute all new whole-box Dirichlet energy payments."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
from n26_force import load_trig
import n26_dirichlet_energy as energy
import verify_conditional_force_stage as binding


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
            or not parent["candidate_angle_actual_sealed_published_replay_matched_and_still_bound"]
            or not parent["candidate_angle_prior_all_paid_nodes_and_closed_splits_preserved"]
            or parent["global_optimality_proved"]):
        raise ValueError("Dirichlet extension lacks the accepted current type and angle chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("prior current proof byte changed: " + text)
    inventory[linux(args.parent_audit)] = binding.sha(args.parent_audit)
    report, files = binding.bound(args.overlay)
    if (binding.read(args.overlay_replay) != report
            or report["schema"] != "N26-accepted-current-candidate-Dirichlet-energy-overlay-v1"
            or report["radius_scope"] != "same-root-Rstar"
            or not report["all_source_nodes_paid_leaves_and_closed_splits_preserved"]
            or not report["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]
            or report["source_OPEN_boxes"] != parent["candidate_angle_unresolved_closed_boxes"]
            or F(report["radius_upper"]) != F(parent["r_strict_interval"][1])
            or report["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or binding.sha(energy.__file__) != report["files"]["n26_dirichlet_energy.py"]):
        raise ValueError("Dirichlet extension has no matching actual sealed replay or changed its root")
    manifest = binding.read(args.overlay / "MANIFEST.json")
    source_folder = binding.local_path(manifest["source"])
    source_acceptance = source_folder / "VERIFIED.json"
    source_certificate = source_folder / "CERTIFICATE.json"
    source_pending = source_folder / "PENDING-ANGLES.json"
    if (inventory.get(linux(source_acceptance)) != report["source_acceptance_sha256"]
            or inventory.get(linux(source_certificate)) != binding.sha(args.overlay / "SOURCE-CERTIFICATE.json")
            or binding.read(source_certificate) != binding.read(args.overlay / "SOURCE-CERTIFICATE.json")
            or binding.read(source_acceptance) != binding.read(args.overlay / "SOURCE-ACCEPTANCE.json")):
        raise ValueError("Dirichlet source tree is not the unchanged current bound tree")
    source_manifest = binding.read(source_folder / "MANIFEST.json")
    pinning_folder = binding.local_path(source_manifest["sources"]["pinning"])
    reference_path = pinning_folder / "CERTIFICATE.json"
    if inventory.get(linux(reference_path)) != binding.sha(reference_path):
        raise ValueError("Dirichlet rod network is not in the current exact root chain")
    reference = binding.read(reference_path)
    kernel = energy.kernel_gate(reference, binding.read(args.overlay / "DIRICHLET-KERNEL.json"))
    certificate = binding.read(args.overlay / "CERTIFICATE.json")
    pending = binding.read(source_pending)
    indices = certificate["paid_source_OPEN_indices"]
    if (certificate["source_tree_sha256"] != binding.sha(source_certificate)
            or len(indices) != len(set(indices)) or any(type(i) is not int for i in indices)
            or certificate["radius_scope"] != "same-root-Rstar"
            or certificate["source_acceptance_sha256"] != report["source_acceptance_sha256"]):
        raise ValueError("Dirichlet paid leaf ownership or conditional radius changed")
    arcs, radius = load_trig(args.overlay)[0], F(report["radius_upper"])
    payments, remaining = [], []
    for row in pending:
        if row["index"] not in indices:
            remaining.append(row)
            continue
        result = energy.bound(row["sharp_lower"], row["sharp_upper"], kernel, radius**2, arcs)
        if not result["radius_conditional_whole_angle_box_excluded"]:
            raise ValueError("new Dirichlet energy leaf has no strict whole-box exclusion")
        payments.append({**row, "kind": "DIRICHLET_EMPTY", **result})
    if (payments != binding.read(args.overlay / "LOWER-LEDGER.json")
            or remaining != binding.read(args.overlay / "PENDING-ANGLES.json")
            or len(payments) != len(indices)
            or len(payments) != report["new_strict_whole_box_Dirichlet_energy_exclusions"]
            or len(remaining) != report["unresolved_closed_angle_boxes"]
            or len(payments) + len(remaining) != len(pending)):
        raise ValueError("Dirichlet overlay lost a paid, unvisited or still-unclosed source leaf")
    files.extend([args.overlay_replay, Path(__file__), Path(energy.__file__), args.narrative])
    for path in files:
        key, digest = linux(path), binding.sha(path)
        if key in inventory and inventory[key] != digest:
            raise ValueError("Dirichlet and previous inventories disagree")
        inventory[key] = digest
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("Dirichlet current bytes changed during final binding")
    result = {
        "schema": "N26-current-full-chain-Dirichlet-candidate-extension-audit-v1",
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "prior_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "conditional_stage_native_and_exact_actual_replays_still_bound": True,
        "new_conditional_stage_strict_whole_subtrees_excluded":
            parent["new_conditional_stage_strict_whole_subtrees_excluded"],
        "type_registry_actual_sealed_published_replay_still_bound": True,
        "strict_radius_conditional_current_type_exclusions":
            parent["strict_radius_conditional_current_type_exclusions"],
        "new_complete_terminal_paths_removed": parent["new_complete_terminal_paths_removed"],
        "unresolved_current_competitor_types": parent["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": parent["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": parent["Rstar_conditional_frontier_pending_subtrees"],
        "Rstar_conditional_frontier_families": parent["Rstar_conditional_frontier_families"],
        "current_candidate_type_paths": parent["current_candidate_type_paths"],
        "all_isomorphic_candidate_terminal_paths_retained": True,
        "known_candidate_unique_complete_34_face_terminal": parent["known_candidate_unique_complete_34_face_terminal"],
        "candidate_angle_new_strict_force_leaves": parent["candidate_angle_new_strict_force_leaves"],
        "candidate_Dirichlet_actual_sealed_published_replay_matched_and_still_bound": True,
        "all_new_Dirichlet_inverse_identities_and_whole_box_energy_payments_recomputed_here": True,
        "candidate_Dirichlet_source_OPEN_boxes": len(pending),
        "candidate_Dirichlet_new_strict_whole_box_exclusions": len(payments),
        "candidate_angle_unresolved_closed_boxes": len(remaining),
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": True,
        "all_siblings_unclosed_types_OPEN_boxes_and_previous_proofs_retained": True,
        "original_U_current_pending_subtrees_unchanged": parent["original_U_current_pending_subtrees_unchanged"],
        "original_U_frontier_nodes_removed_by_conditional_bundles": 0,
        "r_strict_interval": parent["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "radius_scope": parent["radius_scope"],
        "Fejes_Toth_eight_disk_lower_bound_remains_external_dependency": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "files": inventory}
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
