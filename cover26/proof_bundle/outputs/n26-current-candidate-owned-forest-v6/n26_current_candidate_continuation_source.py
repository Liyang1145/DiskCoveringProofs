"""Exact current source after the accepted seven-root continuation.

This fresh gate folds the continuation schema explicitly. It neither gives a
continuation bundle to the old base-forest gate nor creates a new payment.
"""

from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import verify_current_candidate_energy_local_forests as accepted_forest
import verify_conditional_force_stage as binding


read, sha, local_path = binding.read, binding.sha, binding.local_path


def gate(folder, replay_path, current_audit_path, digest_recheck_path):
    current, rehash = read(current_audit_path), read(digest_recheck_path)
    if (
        not current["current_bound_bytes_rechecked"]
        or not current["prior_completed_full_chain_semantic_replay_still_bound"]
        or current["radius_scope"] != binding.SCOPE
        or current["global_optimality_proved"] is not False
        or current["global_lower_bound_proved"] is not False
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or rehash["current_audit_sha256"] != sha(current_audit_path)
        or rehash["all_current_file_digests_rehashed"] is not True
        or rehash["current_file_digests_rechecked"] != len(current["files"])
    ):
        raise ValueError("continuation source lacks the fully audited current chain and final rehash")
    print("Checking every current dependency before folding the accepted continuation.", flush=True)
    inventory = []
    for text, digest in current["files"].items():
        if sha(text) != digest:
            raise ValueError("current continuation dependency changed: " + text)
        inventory.append(local_path(text))
    acceptance, paths = binding.bound(folder)
    inventory.extend(paths)
    if (
        acceptance["schema"] != "N26-accepted-current-candidate-energy-LOCAL-continuation-forests-v1"
        or read(replay_path) != acceptance
        or current["files"].get(linux(folder / "VERIFIED.json")) != sha(folder / "VERIFIED.json")
        or current["files"].get(linux(replay_path)) != sha(replay_path)
        or current["files"].get(linux(folder / "PENDING-ANGLES.json")) != sha(folder / "PENDING-ANGLES.json")
        or sha(accepted_forest.__file__) != acceptance["files"]["verify_current_candidate_energy_local_forests.py"]
        or current.get("actual_current_candidate_acceptance") != linux(folder / "VERIFIED.json")
        or current.get("actual_current_candidate_pending_angles") != linux(folder / "PENDING-ANGLES.json")
    ):
        raise ValueError("continuation source is not the exact current published candidate acceptance")
    print("Reconstructing all prior source payments and the accepted continuation forests.", flush=True)
    values = accepted_forest.input_gate(folder)
    payments, pending, results, boxes, ledgers = accepted_forest.derive(values)
    original_values, incoming = values[3], values[4]
    positive = accepted_forest.base.source.tiny_control(original_values)
    outputs = {
        "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": pending,
        "ROOT-CLASSIFICATION.json": results, "PENDING-FOREST-LEAVES.json": boxes,
        "LOWER-LEDGER.json": ledgers, "POSITIVE-CONTROLS.json": positive,
    }
    if any(read(folder / name) != data for name, data in outputs.items()):
        raise ValueError("current continuation semantic outputs did not reconstruct")
    indices = [row["source_OPEN_index"] for row in payments]
    certificate = read(folder / "CERTIFICATE.json")
    if (
        acceptance["radius_scope"] != "same-root-Rstar"
        or acceptance["source_actual_remaining_candidate_roots"] != len(incoming)
        or acceptance["new_whole_candidate_source_roots_lower_bounded"] != len(payments)
        or acceptance["unresolved_closed_angle_boxes"] != len(pending)
        or current["candidate_angle_unresolved_closed_boxes"] != len(pending)
        or rehash["candidate_angle_unresolved_closed_boxes"] != len(pending)
        or certificate["discharged_actual_source_root_indices"] != indices
        or certificate["LOCAL_lower_bound_is_not_an_emptiness_claim"] is not True
        or certificate["all_unattempted_or_incompletely_proved_source_roots_retained"] is not True
        or len(set(indices)) != len(indices)
        or len(incoming) != len(payments) + len(pending)
        or [row for row in incoming if row["index"] not in indices] != pending
        or any(not row["source_candidate_root_fully_lower_bounded"] for row in payments)
        or any(row["source_candidate_root_strictly_empty"] and row["counts"]["LOCAL"] for row in payments)
        or positive["known_feasible_root_tiny_box_not_energy_excluded"] is not True
        or positive["original_LOCAL_leaf_and_52_coordinate_allowance_preserved"] is not True
        or acceptance["original_92_rod_kernel_and_52_coordinate_frame_preserved"] is not True
    ):
        raise ValueError("current continuation lost complete-root ownership or LOCAL equality feasibility")
    parent_path = local_path(values[0]["parent_current_audit"])
    proof_parent = values[1]
    if (
        current["files"].get(linux(parent_path)) != sha(parent_path)
        or any(current["files"].get(text) != digest for text, digest in proof_parent["files"].items())
        or proof_parent["r_strict_interval"] != current["r_strict_interval"]
        or F(original_values[3]["radius"]) != F(current["r_strict_interval"][1])
        or F(acceptance["radius_upper"]) != F(original_values[3]["radius"])
    ):
        raise ValueError("current continuation lost its identical bound ancestor or original root radius")
    inventory.extend(values[-1])
    inventory.extend((current_audit_path, digest_recheck_path, replay_path, Path(__file__)))
    return acceptance, original_values, pending, inventory, payments
