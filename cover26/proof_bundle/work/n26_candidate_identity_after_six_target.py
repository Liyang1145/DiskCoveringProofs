"""Explicit candidate ancestry through the NEW six-target enumeration schema.

Never relabel a new enumeration supplement as an old schema, reset a newer
candidate layer, or call identity checks actual graph/geometry acceptance.
"""

from audit_prefix_partition import linux
import n26_candidate_identity_with_mixed_curvature as previous
import verify_conditional_force_stage as binding


SIX_SCHEMA = "N26-complete-current-with-six-target-source-geometry-audit-v1"
CURRENT_SCHEMA = previous.CURRENT_SCHEMA


def gate(current, current_sha256, folder, *, reader=None, hasher=None):
    if current["schema"] != SIX_SCHEMA:
        return previous.gate(current, current_sha256, folder, reader=reader, hasher=hasher)
    reader = binding.read if reader is None else reader
    hasher = binding.sha if hasher is None else hasher
    digest = previous.original.digest_gate(current_sha256)
    if (
        current["current_bound_bytes_rechecked"] is not True
        or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or current["six_target_actual_own_publication_and_current_semantic_reports_equal"] is not True
        or current["six_target_full_current_semantic_exit_code"] != 0
        or current["six_target_candidate_whole_roots_removed"] != 0
        or current["candidate_layer_and_all_latest_partial_histories_unchanged_by_six_target_rule"] is not True
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or current["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or current["six_target_new_strict_whole_source_prefixes"] != 5546
        or current["six_target_source_conditional_pending_subtrees"] != 11183
        or current["radius_scope"] != binding.SCOPE
        or current["original_U_current_pending_subtrees_unchanged"] != 3922
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or any(current[field] is not False for field in (
            "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(field in current for field in previous.original.POINTERS)
    ):
        raise ValueError("new six-target schema is not an unchanged-candidate enumeration supplement")
    parent_path = binding.local_path(current["six_target_parent_audit_file"])
    parent_digest = previous.original.digest_gate(current["prior_current_audit_sha256"])
    if (
        parent_digest == digest or hasher(parent_path) != parent_digest
        or current["files"].get(linux(parent_path)) != parent_digest
    ):
        raise ValueError("six-target candidate ancestry cycle or missing/changed actual parent")
    parent = reader(parent_path)
    if (
        parent["candidate_angle_unresolved_closed_boxes"] != current["candidate_angle_unresolved_closed_boxes"]
        or parent["r_strict_interval"] != current["r_strict_interval"]
        or any(current["files"].get(text) != value for text, value in parent["files"].items())
    ):
        raise ValueError("six-target supplement lost its actual candidate/old proof ancestry")
    layer = previous.gate(parent, parent_digest, folder, reader=reader, hasher=hasher)
    if layer != current["six_target_actual_prior_candidate_layer_identity"]:
        raise ValueError("six-target supplement's recorded latest candidate identity does not match its real parent")
    result = dict(layer)
    result["schema"] = "N26-candidate-identity-through-six-target-enumeration-supplement-v1"
    result["actual_current_parent_sha256"] = current_sha256
    result["enumeration_only_bound_ancestors_followed"] = [{
        "new_enumeration_schema": SIX_SCHEMA,
        "actual_six_target_current_sha256": current_sha256,
        "bound_parent_path": linux(parent_path), "sha256": parent_digest,
    }, *layer["enumeration_only_bound_ancestors_followed"]]
    result["explicit_NEW_six_schema_not_relabelled_as_old_enumeration"] = True
    result["identity_only_NOT_current_final_or_whole_geometry_acceptance"] = True
    return result
