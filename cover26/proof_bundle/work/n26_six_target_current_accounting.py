"""Independent complete source/current accounting for actual six-target geometry.

The continuous geometric manuscript and real own/publication/current mains
are prerequisites; these pure checks do not manufacture geometry acceptance.
"""

from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations

import n26_six_target_filled_ears as rule
import test_six_target_filled_boundary_ears as independent


CURRENT_SCHEMA = "N26-complete-current-with-six-target-source-geometry-audit-v1"
ACCEPTANCE_SCHEMA = "N26-actual-whole-source-six-target-filled-ear-geometry-acceptance-v1"
CHECKER = "verify_six_target_source_geometry.py"
MODE = "N26-six-core-target-filled-original-owner-ear-v1"
SCOPE = "at-most-same-root-Rstar-not-original-U"
U = F(234701, 1000000)


def independent_targets():
    radius = 1-2*U
    points = [(F(0), F(0)), (radius/2, radius/2), (radius/2, -radius/2),
              (-radius/2, radius/2), (-radius/2, -radius/2), (-radius, F(0))]
    squared = [(a[0]-b[0])**2+3*(a[1]-b[1])**2 for a, b in combinations(points, 2)]
    separation = F(4, 5)-U-max(x for x, y in points)
    if (
        min(squared) != radius**2 or min(squared) <= 4*U**2
        or any(x*x+3*y*y > radius**2 for x, y in points)
        or separation != F(3, 10) or separation <= U
    ):
        raise ValueError("independent six-target exact continuous-witness inequalities failed")
    return {
        "exact_six_targets_x_and_sqrt3_y_coefficients": [[str(x), str(y)] for x, y in points],
        "exact_core_radius": str(radius),
        "exact_minimum_squared_pair_distance": str(min(squared)),
        "exact_squared_pair_margin_above_four_U_squared": str(min(squared)-4*U**2),
        "exact_ear_to_all_targets_horizontal_distance_lower": str(separation),
        "exact_horizontal_margin_above_U": str(separation-U),
        "six_DISTINCT_ORIGINAL_outside_nonowner_disks_required": 6,
        "finite_identities_do_NOT_replace_the_written_continuous_cover_and_embedding_proof": True,
    }


def receipt_gate(parent, parent_digest, final_digest, accepted, publication, semantic,
                 checker_digest, layer):
    if (
        accepted != publication or accepted != semantic
        or accepted["schema"] != ACCEPTANCE_SCHEMA or accepted["verified"] is not True
        or accepted["radius_scope"] != SCOPE or accepted["inherited_source_is_unconditional_at_U"] is not False
        or accepted["executed_checker_file"] != CHECKER
        or accepted["executed_checker_sha256"] != checker_digest or accepted["files"][CHECKER] != checker_digest
        or accepted["actual_parent_current_sha256"] != parent_digest
        or accepted["actual_parent_final_sha256"] != final_digest
        or accepted["actual_candidate_layer_identity"] != layer
        or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
        or accepted["r_strict_interval"] != parent["r_strict_interval"]
        or F(accepted["screen_radius_threshold_for_NEW_six_target_rule"]) != U
        or accepted["complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER"] is not True
        or accepted["prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA"] is not True
        or accepted["all_original_candidate_terminals_owned_roots_histories_and_LOCAL_retained"] is not True
        or accepted["all_original_counts_AND_shadow_label_placements_freshly_checked_both_ways"] is not True
        or accepted["corner_shadow_is_embedded_LIMIT_NOT_26_positive_area_Voronoi_cells"] is not True
        or accepted["written_continuous_cover_embedding_and_six_target_proofs_used_NOT_inferred_from_finite_tests"] is not True
        or accepted["old643_scope_NOT_used_as_acceptance_of_additional4903"] is not True
        or accepted["fresh_independent_universal_bridge_scalar_identities"] != 12
        or accepted["historical_closed_types_retained"] != 87
        or accepted["historical_proof_receipts_retained_and_associated"] != 215
        or accepted["source_actual_current_frontier"] != 11183
        or accepted["geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL"] != 5637
        or accepted["strict_new_six_target_whole_source_prefixes"] != 5546
        or len(accepted["actual_geometric_scope_negative_controls_rejected"]) != 6
        or any(accepted[field] != 0 for field in (
            "actual_current_nodes_removed_by_this_OWN_acceptance",
            "new_formal_geometric_payments_by_this_OWN_acceptance",
            "candidate_whole_roots_removed", "original_U_frontier_nodes_removed"))
        or any(accepted[field] is not False for field in (
            "unrestricted_reduction_final_joint_acceptance", "frozen_geometric_reduction_proved",
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(accepted["source_files"].get(text) != digest for text, digest in parent["files"].items())
    ):
        raise ValueError("six-target current lacks real unchanged own/publication/whole-current geometry")
    body = accepted["ENTIRE_actual_source_prefixes_six_target_geometry_and_case_partition_replayed_here"]
    if (
        body["entire_actual_original_source_prefixes_reconstructed"] != 11183
        or body["six_target_strict_whole_prefixes"] != 5546
        or body["all_original_physical_count_AND_shadow_label_cases_checked"] != 58916
        or body["distinct_patch_locators_AND_original_vs_shadow_set_enumerations_agreed"] is not True
        or body["all_raw_complete_candidate_and_competitor_terminals_retained_identically"] is not True
        or body["prefix_free_entire_source_and_unpaid_sibling_partition_checked"] is not True
        or body["fresh_independent_exact_six_core_target_identities"] != independent_targets()
    ):
        raise ValueError("six-target own receipt substituted a partial source, case set or witness")


def partition_gate(parent, source, frontier, ledger, constants, proofs):
    rule.family_gate(constants)
    targets = independent_targets()
    if (
        source["N"] != 26 or source["radius_scope"] != SCOPE
        or source["inherited_source_is_unconditional_at_U"] is not False
        or not 0 < F(source["radius_upper"]) < U
        or F(source["radius_upper"]) != F(parent["r_strict_interval"][1])
        or source["families"] != parent["Rstar_conditional_frontier_families"]
        or len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
        or set(proofs) != {"cap", "generic", "bridge", "ear", "six"}
        or any(not isinstance(value, str) or len(value) != 64
               or any(c not in "0123456789abcdef" for c in value) for value in proofs.values())
    ):
        raise ValueError("independent six-target accounting substituted source/radius/proof scope")
    payments = {}
    for row in ledger:
        index = row["source_index"]
        if type(index) is not int or not 0 <= index < len(source["pending_states"]) or index in payments:
            raise ValueError("invalid or duplicate six-target whole-prefix ownership")
        payments[index] = row
    seen, kept, expected_ledger, case_count = set(), [], [], 0
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("duplicate whole source-prefix ownership")
        seen.add(key)
        found = independent.independent_patches(row)
        if not found:
            if index in payments:
                raise ValueError("a non-filled prefix was paid by the six-target rule")
            kept.append(row)
            continue
        if row["terminal"] or index not in payments:
            raise ValueError("a raw terminal was paid, or a qualifying whole prefix was omitted")
        selected = max(found, key=lambda patch: len(patch["actual_enclosed_nonowner_labels"]))
        cases = independent.independent_original_cases(row, selected)
        count = sum(item["all_shadow_label_placements_checked"] for item in cases)
        expected = {
            "mode": MODE, "source_index": index, "B": row["B"], "prefix": row["prefix"],
            "actual_entire_source_state": row, "all_qualifying_filled_patches": found,
            "selected_strongest_filled_patch": selected,
            "all_original_physical_count_and_shadow_case_distributions": cases,
            "original_count_and_shadow_cases_checked": count,
            "continuous_proof_sha256": proofs, "exact_six_core_target_identities": targets,
            "outside_budget_INCLUDES_introduced_outside_vertices_AND_future_labels": True,
            "original_owner_frame_NOT_26_distinct_shadow_Voronoi_cells": True,
            "whole_source_angular_domain_and_ALL_descendant_continuations_excluded": True,
            "exclusion_uses_actual_core_coverage_AND_embedded_filled_patch_NOT_only_weak_rods": True,
            "formal_payment_requires_actual_source_geometry_publication_current_AND_independent_final": True,
        }
        if payments[index] != expected:
            raise ValueError("six-target original case, patch, source state or continuous proof changed")
        expected_ledger.append(expected)
        case_count += count
    if ledger != expected_ledger:
        raise ValueError("six-target ledger contains extra or reordered ownership")
    if any((b, prefix[:length]) in seen for b, prefix in seen for length in range(len(prefix))):
        raise ValueError("source prefixes overlap an ancestor/descendant pair")
    expected = deepcopy(source)
    expected["schema"] = "N26-six-core-target-filled-ear-filtered-conditional-frontier-v1"
    expected["pending_states"] = kept
    conservation = []
    for family in expected["families"]:
        b = family["B"]
        incoming = sum(row["B"] == b for row in source["pending_states"])
        removed = sum(row["B"] == b for row in ledger)
        outgoing = sum(row["B"] == b for row in kept)
        terminals = sum(row["B"] == b and row["terminal"] for row in kept)
        if incoming != family["pending_subtrees"] or incoming != outgoing+removed:
            raise ValueError("independent six-target family conservation differs")
        family.update({
            "six_core_target_filled_ear_whole_subtrees": removed, "pending_subtrees": outgoing,
            "unresolved_terminal_subtrees": terminals, "family_exhausted": outgoing == 0,
        })
        conservation.append({
            "B": b, "actual_source_subtrees": incoming,
            "strict_six_target_whole_subtrees": removed, "retained_subtrees": outgoing,
            "all_raw_terminals_retained": terminals,
        })
    if (
        frontier != expected or len(source["pending_states"]) != 11183
        or len(ledger) != 5546 or len(kept) != 5637 or case_count != 58916
        or [family["pending_subtrees"] for family in expected["families"]] != [296, 694, 2703, 1944]
        or [row for row in kept if row["terminal"]] != [
            row for row in source["pending_states"] if row["terminal"]]
    ):
        raise ValueError("independent six-target full partition omitted an unpaid sibling or raw terminal")
    return {
        "entire_source_prefixes_independently_scanned": len(source["pending_states"]),
        "strict_six_target_whole_prefixes": len(ledger),
        "retained_unpaid_source_prefixes": len(kept),
        "original_physical_count_and_all_shadow_cases": case_count,
        "independent_family_conservation": conservation,
        "independent_exact_six_core_target_identities": targets,
        "all_unpaid_siblings_and_raw_terminals_retained_identically": True,
        "entire_actual_source_prefix_partition_prefix_free": True,
        "candidate_whole_roots_removed": 0,
    }


def current_gate(current, parent, result, layer):
    families = deepcopy(parent["Rstar_conditional_frontier_families"])
    for family, counts in zip(families, result["independent_family_conservation"]):
        if family["B"] != counts["B"]:
            raise ValueError("six-target current changed family ordering")
        family.update({
            "six_core_target_filled_ear_whole_subtrees": counts["strict_six_target_whole_subtrees"],
            "pending_subtrees": counts["retained_subtrees"],
            "unresolved_terminal_subtrees": counts["all_raw_terminals_retained"],
            "family_exhausted": counts["retained_subtrees"] == 0,
        })
    if (
        current["schema"] != CURRENT_SCHEMA or current["current_bound_bytes_rechecked"] is not True
        or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or current["six_target_actual_own_publication_and_current_semantic_reports_equal"] is not True
        or current["six_target_full_current_semantic_exit_code"] != 0
        or current["independent_exact_six_target_source_accounting"] != result
        or current["six_target_actual_prior_candidate_layer_identity"] != layer
        or current["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or current["Rstar_conditional_frontier_families"] != families
        or current["six_target_new_strict_whole_source_prefixes"] != 5546
        or current["six_target_source_conditional_pending_subtrees"] != 11183
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or current["six_target_candidate_whole_roots_removed"] != 0
        or current["original_U_current_pending_subtrees_unchanged"] != 3922
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or current["radius_scope"] != SCOPE or current["r_strict_interval"] != parent["r_strict_interval"]
        or current["joined_closed_full_type_codes_in_these_two_catalogues"] != 87
        or current["all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"] != 215
        or any(current[field] != parent[field] for field in (
            "all_current_competitor_terminal_obligations_explicitly_retained",
            "current_candidate_type_paths", "known_candidate_unique_complete_34_face_terminal"))
        or any(current[field] is not False for field in (
            "inherited_source_is_unconditional_at_U", "unrestricted_reduction_final_joint_acceptance",
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(current["files"].get(text) != digest for text, digest in parent["files"].items())
    ):
        raise ValueError("six-target current changed original scope, candidate histories or accepted parent evidence")
