"""Explicit candidate ancestry through NEW midarc enumeration, not relabelling.

This is identity only. A real full-current semantic main and independent final
are mandatory elsewhere. Old sealed dispatchers are unchanged.
"""

from audit_prefix_partition import linux
import n26_candidate_identity_after_six_target as previous
import verify_conditional_force_stage as binding


CURRENT_SCHEMA = "N26-complete-current-with-midarc-source-geometry-audit-v1"
POINTERS = (*previous.previous.original.POINTERS, "actual_current_candidate_remaining_history")


def gate(current, current_sha256, folder, *, reader=None, hasher=None):
    if current["schema"] != CURRENT_SCHEMA:
        return previous.gate(current, current_sha256, folder, reader=reader, hasher=hasher)
    reader = binding.read if reader is None else reader
    hasher = binding.sha if hasher is None else hasher
    digest = previous.previous.original.digest_gate(current_sha256)
    if (
        current["current_bound_bytes_rechecked"] is not True
        or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or current["midarc_actual_own_publication_and_current_semantic_reports_equal"] is not True
        or current["midarc_full_current_semantic_exit_code"] != 0
        or current["midarc_candidate_whole_roots_removed"] != 0
        or current["candidate_layer_and_all_latest_partial_histories_unchanged_by_midarc_rule"] is not True
        or current["candidate_angle_unresolved_closed_boxes"] != 16
        or current["Rstar_conditional_frontier_pending_subtrees"] != 4957
        or current["midarc_source_conditional_pending_subtrees"] != 5637
        or current["midarc_new_strict_whole_source_prefixes"] != 680
        or current["radius_scope"] != binding.SCOPE
        or current["original_U_current_pending_subtrees_unchanged"] != 3922
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or any(current[field] is not False for field in (
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(field in current for field in POINTERS)
    ):
        raise ValueError("NEW midarc schema is not an unchanged16-root enumeration supplement")
    parent_path = binding.local_path(current["midarc_parent_audit_file"])
    parent_digest = previous.previous.original.digest_gate(current["prior_current_audit_sha256"])
    if (
        parent_digest == digest or hasher(parent_path) != parent_digest
        or current["files"].get(linux(parent_path)) != parent_digest
    ):
        raise ValueError("midarc candidate ancestry cycle or missing/changed actual parent")
    parent = reader(parent_path)
    if (
        parent["schema"] != previous.CURRENT_SCHEMA
        or parent["candidate_angle_unresolved_closed_boxes"] != 16
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or parent["r_strict_interval"] != current["r_strict_interval"]
        or any(current["files"].get(text) != value for text, value in parent["files"].items())
    ):
        raise ValueError("midarc supplement lost actual mixed16-root ancestry or old proof dependencies")
    layer = previous.gate(parent, parent_digest, folder, reader=reader, hasher=hasher)
    if layer != current["midarc_actual_prior_candidate_layer_identity"]:
        raise ValueError("midarc recorded latest candidate identity differs from its real bound parent")
    result = dict(layer)
    result.update({
        "schema": "N26-candidate-identity-through-midarc-enumeration-supplement-v1",
        "actual_current_parent_sha256": current_sha256,
        "enumeration_only_bound_ancestors_followed": [{
            "new_enumeration_schema": CURRENT_SCHEMA,
            "actual_midarc_current_sha256": current_sha256,
            "bound_parent_path": linux(parent_path), "sha256": parent_digest,
        }, *layer["enumeration_only_bound_ancestors_followed"]],
        "explicit_NEW_midarc_schema_not_relabelled_as_old_enumeration_or_mixed_candidate_admission": True,
        "identity_only_NOT_current_final_or_whole_model_geometry_acceptance": True,
    })
    return result
