"""Complete latest source replay with separate formal and candidate-owner pairs.

No typed arithmetic context, diagnostic producer or faster geometry cache is
imported. The actual owned/mixed/product source gate is invoked in full.
"""

from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_with_product_forests as identity
import n26_current_owned_candidate_source as owned
import n26_current_mixed_curvature_candidate_source as mixed
import n26_current_product_candidate_source as product
import verify_conditional_force_stage as binding


SCHEMA = "N26-distinct-formal-and-candidate-owner-complete-source-replay-v1"
DISPATCH = {
    owned.SCHEMA: owned,
    mixed.checker.SCHEMA: mixed,
    product.checker.SCHEMA: product,
}


def pair_gate(current, final, digest):
    if (current["current_bound_bytes_rechecked"] is not True
            or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
            or current["radius_scope"] != binding.SCOPE
            or current["global_lower_bound_proved"] is not False
            or current["global_optimality_proved"] is not False
            or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or current["original_U_current_pending_subtrees_unchanged"] != 3922
            or final["current_audit_sha256"] != digest
            or final["all_current_file_digests_rehashed"] is not True
            or final["current_file_digests_rechecked"] != len(current["files"])
            or final["candidate_angle_unresolved_closed_boxes"]
            != current["candidate_angle_unresolved_closed_boxes"]
            or final["global_lower_bound_proved"] is not False
            or final["global_optimality_proved"] is not False):
        raise ValueError("complete source replay lacks an actual matching current/final pair")


def preflight(source, replay_path, formal_path, formal_final_path,
              owner_path, owner_final_path, *, reader=None, hasher=None, identifier=None):
    """Identity/inventory association ONLY; not a model or geometry replay."""
    reader = binding.read if reader is None else reader
    hasher = binding.sha if hasher is None else hasher
    identifier = identity.gate if identifier is None else identifier
    source, replay_path, formal_path, formal_final_path, owner_path, owner_final_path = (
        binding.local_path(path) for path in
        (source, replay_path, formal_path, formal_final_path, owner_path, owner_final_path))
    formal, final = reader(formal_path), reader(formal_final_path)
    owner, owner_final = reader(owner_path), reader(owner_final_path)
    formal_digest, owner_digest = hasher(formal_path), hasher(owner_path)
    pair_gate(formal, final, formal_digest)
    pair_gate(owner, owner_final, owner_digest)
    formal_layer = identifier(formal, formal_digest, source, reader=reader, hasher=hasher)
    owner_layer = identifier(owner, owner_digest, source, reader=reader, hasher=hasher)
    if (formal_layer["latest_candidate_current_audit_sha256"] != owner_digest
            or owner_layer["latest_candidate_current_audit_sha256"] != owner_digest
            or formal_layer["actual_latest_candidate_acceptance_sha256"]
            != owner_layer["actual_latest_candidate_acceptance_sha256"]
            or formal_layer["actual_latest_candidate_pending_angles_sha256"]
            != owner_layer["actual_latest_candidate_pending_angles_sha256"]
            or formal["candidate_angle_unresolved_closed_boxes"]
            != owner["candidate_angle_unresolved_closed_boxes"]
            or formal["r_strict_interval"] != owner["r_strict_interval"]
            or any(formal["files"].get(text) != digest
                   for text, digest in owner["files"].items())):
        raise ValueError("candidate-owner pair is not the actual identically bound latest source owner")
    if formal_path.resolve() != owner_path.resolve():
        for path in (owner_path, owner_final_path):
            if formal["files"].get(linux(path)) != hasher(path):
                raise ValueError("candidate-owner current/final ancestor is missing from formal inventory")
    elif formal_final_path.resolve() != owner_final_path.resolve():
        raise ValueError("same current path supplied with a different final snapshot")
    accepted = reader(source / "VERIFIED.json")
    checker = DISPATCH.get(accepted["schema"])
    if (checker is None or accepted["verified"] is not True
            or accepted["radius_scope"] != "same-root-Rstar"
            or accepted["global_optimality_proved"] is not False
            or accepted["unresolved_closed_angle_boxes"]
            != formal["candidate_angle_unresolved_closed_boxes"]
            or F(accepted["radius_upper"]) != F(formal["r_strict_interval"][1])
            or reader(replay_path) != accepted
            or formal["files"].get(linux(replay_path)) != hasher(replay_path)
            or owner["files"].get(linux(replay_path)) != hasher(replay_path)
            or owner.get("actual_current_candidate_acceptance")
            != linux(source / "VERIFIED.json")
            or owner.get("actual_current_candidate_pending_angles")
            != linux(source / "PENDING-ANGLES.json")):
        raise ValueError("complete source replay changed the actual latest source, replay, schema or radius")
    return {
        "schema": SCHEMA,
        "actual_formal_current_sha256": formal_digest,
        "actual_candidate_owner_current_sha256": owner_digest,
        "actual_formal_final_sha256": hasher(formal_final_path),
        "actual_candidate_owner_final_sha256": hasher(owner_final_path),
        "formal_and_candidate_owner_pairs_are_separately_named": True,
        "actual_source_schema": accepted["schema"],
        "actual_latest_candidate_identity": formal_layer,
        "preflight_is_identity_only_NOT_complete_source_model_history_replay": True,
        "new_geometric_payments": 0,
    }


def gate(source, replay_path, formal_path, formal_final_path, owner_path, owner_final_path):
    """Fresh ENTIRE semantic source/model/payment/history replay, not metadata."""
    source, replay_path, formal_path, formal_final_path, owner_path, owner_final_path = (
        binding.local_path(path) for path in
        (source, replay_path, formal_path, formal_final_path, owner_path, owner_final_path))
    association = preflight(
        source, replay_path, formal_path, formal_final_path, owner_path, owner_final_path)
    own_digest = binding.sha(__file__)
    formal = binding.read(formal_path)
    inventory = []
    for number, (text, digest) in enumerate(formal["files"].items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("complete source replay formal dependency changed: "+text)
        inventory.append(binding.local_path(text))
        if number % 10000 == 0:
            print({"complete_source_formal_dependencies_rehashed": number,
                   "total": len(formal["files"])}, flush=True)
    accepted, paths = binding.bound(source)
    inventory.extend(paths)
    backend = DISPATCH[accepted["schema"]]
    print("Replaying ENTIRE actual latest source/model, all original payments and newest history.",
          flush=True)
    # Deliberately call the actual source's ORIGINAL full gate. The formal
    # enumeration descendant is not relabelled as this candidate-owner audit.
    replayed = backend.gate(source, replay_path, owner_path, owner_final_path)
    if backend is owned:
        actual, original_values, incoming, paths, payments = replayed
        history, history_paths = owned.history(source, incoming)
        paths.extend(history_paths)
    else:
        actual, original_values, incoming, paths, payments, history, _ = replayed
    if (actual != accepted
            or len(incoming) != formal["candidate_angle_unresolved_closed_boxes"]
            or F(original_values[3]["radius"]) != F(formal["r_strict_interval"][1])
            or len({row["index"] for row in incoming}) != len(incoming)
            or any(index not in {row["index"] for row in incoming} for index in history)):
        raise ValueError("complete source semantic replay lost exact current ownership or radius")
    inventory.extend(paths)
    inventory.extend((source / "VERIFIED.json", replay_path, formal_path, formal_final_path,
                      owner_path, owner_final_path, Path(__file__), Path(identity.__file__)))
    fresh = preflight(
        source, replay_path, formal_path, formal_final_path, owner_path, owner_final_path)
    if fresh != association or binding.sha(__file__) != own_digest:
        raise ValueError("complete source replay current/source snapshots or own adapter changed")
    return (
        actual, original_values, incoming, inventory, payments, history,
        {**association,
         "preflight_is_identity_only_NOT_complete_source_model_history_replay": False,
         "ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here": True,
         "executed_complete_source_adapter_sha256": own_digest,
         "source_replay_is_NOT_final_candidate_forest_or_unrestricted_joint_acceptance": True},
    )
