"""Pure admission/preservation guards for mixed covers AFTER the actual SIX pair.

These guards are not geometry execution. The separate current executor must
run the entire frozen mixed checker; the independent final rehash must bind
all files and check the exact source rows and remaining histories again.
"""

from fractions import Fraction as F

from audit_prefix_partition import linux
import n26_candidate_identity_after_six_target as identity
import recheck_mixed_curvature_candidate_current as old_final
import verify_conditional_force_stage as binding


CURRENT_SCHEMA = identity.CURRENT_SCHEMA
FINAL_SCHEMA = "N26-independent-mixed-after-six-current-final-rehash-v1"
SIX_FINAL_SCHEMA = "N26-independent-six-target-source-current-final-rehash-v1"
FAMILY_COUNTS = [(14, 296), (15, 694), (16, 2703), (17, 1944)]
CONTROL_COUNT = 34
GLOBAL_FALSE = (
    "full_catalog_complete", "global_lower_bound_proved",
    "global_optimality_proved", "n27_started",
)


def parent_gate(parent, digest, final, frontier, frontier_path, frontier_digest):
    if (
        parent["schema"] != identity.SIX_SCHEMA
        or parent["current_bound_bytes_rechecked"] is not True
        or parent["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or parent["six_target_actual_own_publication_and_current_semantic_reports_equal"] is not True
        or parent["six_target_full_current_semantic_exit_code"] != 0
        or parent["candidate_layer_and_all_latest_partial_histories_unchanged_by_six_target_rule"] is not True
        or parent["six_target_candidate_whole_roots_removed"] != 0
        or parent["six_target_new_strict_whole_source_prefixes"] != 5546
        or parent["candidate_angle_unresolved_closed_boxes"] != 25
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or parent["joined_closed_full_type_codes_in_these_two_catalogues"] != 87
        or parent["all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"] != 215
        or parent["radius_scope"] != binding.SCOPE
        or parent["original_U_current_pending_subtrees_unchanged"] != 3922
        or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or any(parent[field] is not False for field in GLOBAL_FALSE)
        or final["schema"] != SIX_FINAL_SCHEMA
        or final["current_audit_sha256"] != digest
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(parent["files"])
        or final["actual_own_publication_AND_complete_current_semantic_reports_byte_identical"] is not True
        or final["all_actual_latest_owned8_histories_and_raw_terminal_obligations_retained"] is not True
        or final["candidate_angle_unresolved_closed_boxes"] != 25
        or final["candidate_whole_roots_removed"] != 0
        or final["new_strict_whole_prefixes"] != 5546
        or final["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or final["retained_closed_full_type_codes"] != 87
        or final["retained_checked_proof_receipts"] != 215
        or final["radius_scope"] != parent["radius_scope"]
        or final["r_strict_interval"] != parent["r_strict_interval"]
        or any(final[field] is not False for field in GLOBAL_FALSE)
    ):
        raise ValueError("mixed-after-SIX requires the actual completed SIX current/final scope")
    expected_path = linux(frontier_path)
    if (
        parent["current_frontier_actual_file"] != expected_path
        or parent["files"].get(expected_path) != frontier_digest
        or frontier["schema"] != "N26-six-core-target-filled-ear-filtered-conditional-frontier-v1"
        or frontier["N"] != 26
        or frontier["radius_scope"] != binding.SCOPE
        or F(frontier["radius_upper"]) != F(parent["r_strict_interval"][1])
        or len(frontier["pending_states"]) != 5637
        or [(row["B"], row["pending_subtrees"]) for row in frontier["families"]] != FAMILY_COUNTS
        or frontier["families"] != parent["Rstar_conditional_frontier_families"]
        or final["Rstar_conditional_frontier_families"] != frontier["families"]
    ):
        raise ValueError("mixed-after-SIX cannot restore an older transport frontier")


def source_partition_gate(current, accepted, incoming, payments, remaining,
                          history, retained, indices):
    old_final.accounting_gate(
        current, accepted, incoming, payments, remaining, history, retained, indices,
    )
    if (
        accepted["verified"] is not True
        or accepted["source_actual_remaining_candidate_roots"] != 25
        or accepted["new_whole_candidate_source_roots_lower_bounded"] != 9
        or accepted["unresolved_closed_angle_boxes"] != 16
        or accepted["new_strictly_empty_source_roots"] != 0
        or accepted["new_source_roots_discharged_with_original_LOCAL"] != 9
        or accepted["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or accepted["LOCAL_equality_feasible_regions_never_declared_empty"] is not True
        or accepted["original_full_latest_model_source_all_old_payments_and_history_replayed"] is not True
        or accepted["actual_newest_per_root_owned_forests_retained_identically"] is not True
        or accepted["accepted_curvature_modes"] != ["constant-hull", "integrated-Taylor"]
        or len(accepted["negative_controls_rejected"]) != 29
        or indices != [37, 41, 45, 48, 44, 40, 33, 36, 32]
        or [row["index"] for row in remaining] != [
            1, 5, 9, 13, 17, 21, 25, 29, 28, 24, 20, 16, 12, 8, 959, 1023,
        ]
        or [row["source_OPEN_index"] for row in retained] != [959]
    ):
        raise ValueError("mixed-after-SIX must preserve the exact real 25-to-16 source/history partition")


def current_gate(current, parent, digest, frontier, frontier_digest):
    if (
        current["schema"] != CURRENT_SCHEMA
        or current["prior_current_audit_sha256"] != digest
        or current["mixed_after_six_actual_completed_parent_pair_bound"] is not True
        or current["mixed_after_six_frontier_sha256"] != frontier_digest
        or current["current_frontier_actual_file"] != parent["current_frontier_actual_file"]
        or current["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or current["Rstar_conditional_frontier_families"] != frontier["families"]
        or current["radius_scope"] != parent["radius_scope"]
        or current["r_strict_interval"] != parent["r_strict_interval"]
        or current["current_bound_bytes_rechecked"] is not True
        or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or current["mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here"] is not True
        or current["mixed_curvature_actual_full_semantic_exit_code"] != 0
        or current["mixed_curvature_source_is_actual_latest_candidate_layer"] is not True
        or current["all_newest_owned_histories_retained_identically"] is not True
        or current["current_transport_frontier_unchanged_by_mixed_candidate_covers"] is not True
        or current["mixed_curvature_new_whole_source_roots_lower_bounded"] != 9
        or current["mixed_curvature_new_strictly_empty_source_roots"] != 0
        or current["mixed_curvature_new_source_roots_with_original_LOCAL"] != 9
        or current["candidate_angle_unresolved_closed_boxes"] != 16
        or current["remaining_latest_partial_root_histories"] != 1
        or current["original_U_current_pending_subtrees_unchanged"] != 3922
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or current["LOCAL_equality_feasible_regions_never_declared_empty"] is not True
        or current["joined_closed_full_type_codes_in_these_two_catalogues"] != 87
        or current["all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"] != 215
        or current["candidate_transport_global_lower_bound_proved"] is not False
        or any(current[field] is not False for field in GLOBAL_FALSE)
        or any(current["files"].get(text) != value for text, value in parent["files"].items())
    ):
        raise ValueError("mixed-after-SIX current lost actual frontier/evidence/LOCAL or overclaimed global closure")
