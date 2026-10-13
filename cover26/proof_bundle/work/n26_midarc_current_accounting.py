"""Pure complete-current guards for actual NEW680 midarc geometry.

Independent source accounting lives in a separate tested module. Metadata
guards do not execute source geometry or manufacture formal admission.
"""

from copy import deepcopy
from fractions import Fraction as F

import n26_candidate_identity_after_midarc as identity
import n26_midarc_source_accounting as source


CURRENT_SCHEMA = identity.CURRENT_SCHEMA
FINAL_SCHEMA = "N26-independent-midarc-source-current-final-rehash-v1"
CHECKER = source.CHECKER


def receipt_gate(parent, parent_digest, final_digest, accepted, publication, semantic,
                 checker_digest, layer):
    if (
        accepted != publication or accepted != semantic
        or accepted["schema"] != source.ACCEPTANCE_SCHEMA or accepted["verified"] is not True
        or accepted["radius_scope"] != source.SCOPE or accepted["inherited_source_is_unconditional_at_U"] is not False
        or accepted["executed_checker_file"] != CHECKER
        or accepted["executed_checker_sha256"] != checker_digest
        or accepted["files"].get(CHECKER) != checker_digest
        or accepted["actual_parent_current_sha256"] != parent_digest
        or accepted["actual_parent_final_sha256"] != final_digest
        or accepted["actual_candidate_layer_identity"] != layer
        or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
        or accepted["r_strict_interval"] != parent["r_strict_interval"]
        or F(accepted["screen_radius_threshold_for_NEW_midarc_rule"]) != source.U
        or accepted["complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER"] is not True
        or accepted["prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA"] is not True
        or accepted["all_actual16_candidate_roots_histories_and_original_LOCAL_retained"] is not True
        or accepted["all_original_counts_AND_shadow_label_placements_freshly_checked_both_ways"] is not True
        or accepted["corner_shadow_is_embedded_LIMIT_NOT26_positive_area_Voronoi_cells"] is not True
        or accepted["written_continuous_midarc_cover_and_embedding_proofs_used_NOT_inferred_from_finite_tests"] is not True
        or accepted["fresh_independent_universal_bridge_scalar_identities"] != 12
        or accepted["historical_closed_types_retained"] != 87
        or accepted["historical_proof_receipts_retained_and_associated"] != 215
        or accepted["source_actual_current_frontier"] != 5637
        or accepted["geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL"] != 4957
        or accepted["strict_NEW_midarc_whole_source_prefixes"] != 680
        or accepted["old5546_SIX_whole_prefix_payments_preserved_NOT_repaid"] is not True
        or len(accepted["actual_geometric_scope_negative_controls_rejected"]) != 10
        or any(accepted[field] != 0 for field in (
            "actual_current_nodes_removed_by_this_OWN_acceptance",
            "new_formal_geometric_payments_by_this_OWN_acceptance",
            "candidate_whole_roots_removed", "original_U_frontier_nodes_removed"))
        or any(accepted[field] is not False for field in (
            "unrestricted_reduction_final_joint_acceptance", "frozen_geometric_reduction_proved",
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(accepted["source_files"].get(text) != value for text, value in parent["files"].items())
    ):
        raise ValueError("midarc current lacks identical actual own/publication/full-current geometry receipts")
    body = accepted["ENTIRE_actual_source_prefixes_midarc_geometry_and_case_partition_replayed_here"]
    independent = accepted["independent_complete_actual_remaining_source_accounting"]
    if (
        body["entire_actual_ORIGINAL_SIX_filtered_source_prefixes_reconstructed"] != 5637
        or body["strict_NEW_midarc_whole_prefixes"] != 680
        or body["all_original_physical_count_AND_shadow_label_cases_checked"] != 9172
        or body["distinct_patch_locators_AND_original_vs_shadow_set_enumerations_agreed"] is not True
        or body["all_raw_complete_candidate_and_competitor_terminals_retained_identically"] is not True
        or body["prefix_free_entire_source_and_unpaid_sibling_partition_checked"] is not True
        or body["old5546_SIX_whole_prefixes_NOT_repaid"] is not True
        or body["fresh_independent_exact_midarc_core_target_identities"] != source.independent_targets()
        or independent["entire_actual_SIX_filtered_source_prefixes_independently_scanned"] != 5637
        or independent["strict_NEW_midarc_whole_prefixes"] != 680
        or independent["retained_unpaid_source_prefixes"] != 4957
        or independent["original_physical_count_and_all_shadow_cases"] != 9172
        or independent["independent_exact_midarc_core_target_identities"] != source.independent_targets()
        or independent["independent_family_conservation"] != body["family_conservation"]
    ):
        raise ValueError("midarc receipt substituted a partial source/case set or an inexact midpoint-frame witness")


def current_gate(current, parent, result, layer):
    families = deepcopy(parent["Rstar_conditional_frontier_families"])
    for family, counts in zip(families, result["independent_family_conservation"]):
        if family["B"] != counts["B"]:
            raise ValueError("midarc current changed owner family ordering")
        family.update({
            "midarc_filled_patch_NEW_whole_subtrees": counts["strict_NEW_midarc_whole_subtrees"],
            "pending_subtrees": counts["retained_subtrees"],
            "unresolved_terminal_subtrees": counts["all_raw_terminals_retained"],
            "family_exhausted": counts["retained_subtrees"] == 0,
        })
    if (
        current["schema"] != CURRENT_SCHEMA
        or current["current_bound_bytes_rechecked"] is not True
        or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or current["midarc_actual_own_publication_and_current_semantic_reports_equal"] is not True
        or current["midarc_full_current_semantic_exit_code"] != 0
        or current["midarc_independent_exact_source_accounting"] != result
        or current["midarc_actual_prior_candidate_layer_identity"] != layer
        or current["Rstar_conditional_frontier_pending_subtrees"] != 4957
        or current["Rstar_conditional_frontier_families"] != families
        or current["midarc_source_conditional_pending_subtrees"] != 5637
        or current["midarc_new_strict_whole_source_prefixes"] != 680
        or current["candidate_angle_unresolved_closed_boxes"] != 16
        or current["midarc_candidate_whole_roots_removed"] != 0
        or current["candidate_layer_and_all_latest_partial_histories_unchanged_by_midarc_rule"] is not True
        or current["remaining_latest_partial_root_histories"] != parent["remaining_latest_partial_root_histories"]
        or current["original_U_current_pending_subtrees_unchanged"] != 3922
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or current["radius_scope"] != source.SCOPE
        or current["r_strict_interval"] != parent["r_strict_interval"]
        or current["joined_closed_full_type_codes_in_these_two_catalogues"] != 87
        or current["all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"] != 215
        or any(current[field] != parent[field] for field in (
            "all_current_competitor_terminal_obligations_explicitly_retained",
            "current_candidate_type_paths", "known_candidate_unique_complete_34_face_terminal"))
        or any(current[field] is not False for field in (
            "inherited_source_is_unconditional_at_U", "unrestricted_reduction_final_joint_acceptance",
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(field in current for field in identity.POINTERS)
        or any(current["files"].get(text) != value for text, value in parent["files"].items())
    ):
        raise ValueError("midarc current changed actual16-root source/history/LOCAL or lost accepted parent evidence")
