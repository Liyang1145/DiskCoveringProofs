"""Independent exact accounting for a closed-ear current supplement.

This does not execute or impersonate the geometry verifier. It independently
checks the source partition, every original/shadow case, and admission scope.
The written continuous proof and the real geometry main remain prerequisites.
"""

from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations

from test_n26_closed_ear_core_capacity import independent_patch


CURRENT_SCHEMA = "N26-complete-current-with-closed-ear-source-geometry-audit-v1"
ACCEPTANCE_SCHEMA = "N26-actual-whole-source-closed-ear-core-capacity-geometry-acceptance-v1"
CHECKER = "verify_closed_ear_source_geometry.py"
MODE = "N26-closed-ear-core-capacity-original-owner-corner-shadow-v1"
SCOPE = "at-most-same-root-Rstar-not-original-U"
U = F(234701, 1000000)


def receipt_gate(parent, parent_digest, final_digest, accepted, replay, semantic,
                 checker_digest, layer):
    if (
        accepted != replay or accepted != semantic
        or accepted["schema"] != ACCEPTANCE_SCHEMA
        or accepted["verified"] is not True
        or accepted["radius_scope"] != SCOPE
        or accepted["inherited_source_is_unconditional_at_U"] is not False
        or accepted["executed_checker_file"] != CHECKER
        or accepted["executed_checker_sha256"] != checker_digest
        or accepted["files"][CHECKER] != checker_digest
        or accepted["actual_parent_current_sha256"] != parent_digest
        or accepted["actual_parent_final_sha256"] != final_digest
        or accepted["actual_candidate_layer_identity"] != layer
        or accepted["complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER"] is not True
        or accepted["prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA"] is not True
        or accepted["all_original_candidate_terminal_states_owned_roots_histories_and_LOCAL_retained"] is not True
        or accepted["all_original_physical_counts_and_shadow_label_placements_covered"] is not True
        or accepted["corner_copy_is_embedded_LIMIT_not_26_distinct_original_Voronoi_cells"] is not True
        or accepted["written_continuous_dual_starring_and_ear_proofs_are_used_NOT_inferred_from_finite_tests"] is not True
        or accepted["fresh_independent_universal_bridge_scalar_identities"] != 12
        or accepted["historical_closed_types_retained"] != 87
        or accepted["historical_proof_receipts_retained_and_associated"] != 215
        or accepted["source_actual_current_frontier"] != 11183
        or accepted["geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL"] != 10540
        or accepted["strict_new_closed_ear_whole_source_prefixes"] != 643
        or accepted["r_strict_interval"] != parent["r_strict_interval"]
        or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])
        or accepted["screen_radius_threshold_for_NEW_ear_rule"] != str(U)
        or any(accepted[name] != 0 for name in (
            "actual_current_nodes_removed_by_this_OWN_acceptance",
            "new_formal_geometric_payments_by_this_OWN_acceptance",
            "candidate_whole_roots_removed", "original_U_frontier_nodes_removed"))
        or any(accepted[name] is not False for name in (
            "unrestricted_reduction_final_joint_acceptance", "frozen_geometric_reduction_proved",
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(accepted["source_files"].get(text) != digest
               for text, digest in parent["files"].items())
    ):
        raise ValueError("closed-ear current lacks real unchanged own/publication/semantic geometry")
    body = accepted["ENTIRE_actual_source_prefixes_geometry_and_case_partition_replayed_here"]
    if (
        body["entire_actual_source_prefixes_reconstructed"] != 11183
        or body["closed_ear_whole_prefixes"] != 643
        or body["original_physical_count_cases_checked"] != 646
        or body["original_physical_count_AND_all_shadow_label_placement_cases_checked"] != 673
        or body["all_raw_complete_terminals_retained_identically"] is not True
        or body["prefix_free_whole_source_partition_checked"] is not True
    ):
        raise ValueError("closed-ear acceptance substituted a partial source or shadow scan")


def original_shadow_cases(row, constants):
    """Independent cardinality enumeration, not the transfer producer's helper."""
    if (
        constants["N"] != 26 or F(constants["radius_upper"]) != U
        or constants["minimum_interior_cells"] != 9
        or constants["minimum_boundary_cells"] != 14
        or constants["maximum_boundary_cells"] != 17
        or constants["external_n8_theorem_assumed"] is not True
        or constants["n8_reproved_here"] is not False
        or constants["families"] != [[14, 12], [15, 11], [16, 10], [17, 9]]
    ):
        raise ValueError("independent ear accounting lost the original-owner external family premise")
    b, count = row["B"], row["next"]
    if b not in (14, 15, 16, 17) or not b <= count <= 26 or 26-count > 3:
        raise ValueError("independent ear accounting has an invalid remaining-label budget")
    records = []
    labels = tuple(range(b, 26))
    for m in range(b+9, 27):
        for copied in combinations(labels, 26-m):
            originals = tuple(v for v in labels if v not in copied)
            inside = [v for v in originals if v < count]
            outside = [v for v in originals if v >= count]
            if len(originals) != m-b or len(outside) >= 4:
                raise ValueError("four core targets have enough possible outside originals")
            records.append({
                "original_irredundant_physical_disks": m,
                "shadow_labels": list(copied),
                "retained_original_nonowner_labels_inside_filled_ear": inside,
                "retained_original_nonowner_labels_not_yet_introduced": outside,
                "maximum_original_nonowners_available_for_four_core_points": len(outside),
                "four_DISTINCT_ORIGINAL_nonowners_required": 4,
            })
    return records


def partition_gate(parent, source, filtered, ledger, constants, proofs):
    if (
        source["N"] != 26 or source["radius_scope"] != SCOPE
        or source["inherited_source_is_unconditional_at_U"] is not False
        or not 0 < F(source["radius_upper"]) < U
        or F(source["radius_upper"]) != F(parent["r_strict_interval"][1])
        or len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
        or source["families"] != parent["Rstar_conditional_frontier_families"]
        or set(proofs) != {"cap", "generic", "bridge", "ear"}
        or any(not isinstance(value, str) or len(value) != 64
               or any(c not in "0123456789abcdef" for c in value) for value in proofs.values())
    ):
        raise ValueError("independent ear accounting substituted the source, radius or continuous proof")
    rows = source["pending_states"]
    by_index = {}
    for payment in ledger:
        index = payment["source_index"]
        if type(index) is not int or not 0 <= index < len(rows) or index in by_index:
            raise ValueError("invalid or duplicate whole-prefix payment ownership")
        by_index[index] = payment
    kept, paid, seen, cases_checked, m_checked = [], [], set(), 0, 0
    for index, row in enumerate(rows):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("duplicate original source prefix")
        seen.add(key)
        patch = independent_patch(row)
        if patch is None:
            if index in by_index:
                raise ValueError("a non-ear prefix was paid")
            kept.append(row)
            continue
        if row["terminal"] or index not in by_index:
            raise ValueError("a raw terminal was paid, or an actual whole ear was omitted")
        cases = original_shadow_cases(row, constants)
        expected = {
            "mode": MODE, "source_index": index, "B": row["B"], "prefix": row["prefix"],
            "actual_entire_source_state": row, "closed_embedded_limit_patch": patch,
            "original_physical_count_and_all_shadow_label_placement_cases": cases,
            "B17_has_26_original_disks_and_NO_padding": row["B"] == 17,
            "original_owner_count_NOT_augmented_nearest_diagram_count": True,
            "continuous_proof_sha256": proofs,
            "exact_forbidden_ear_projection_lower": str(F(4, 5)-U),
            "exact_projection_margin_above_U": str(F(4, 5)-2*U),
            "exact_core_point_minimum_distance_margin_above_2U": str(1-4*U),
            "whole_source_angular_domain_and_ALL_descendant_continuations_excluded": True,
            "exclusion_is_geometry_and_actual_core_coverage_NOT_only_weak_rods": True,
            "payment_requires_actual_source_geometry_publication_current_and_independent_final": True,
        }
        if by_index[index] != expected:
            raise ValueError("whole-prefix payment, physical/shadow case or continuous proof changed")
        paid.append(expected)
        cases_checked += len(cases)
        m_checked += 27-(row["B"]+9)
    if ledger != paid:
        raise ValueError("whole-prefix ledger has extra or reordered ownership")
    if any((b, prefix[:length]) in seen
           for b, prefix in seen for length in range(len(prefix))):
        raise ValueError("original source contains overlapping ancestor/descendant ownership")
    expected = deepcopy(source)
    expected["schema"] = "N26-closed-ear-core-capacity-filtered-conditional-frontier-v1"
    expected["pending_states"] = kept
    conservation = []
    for family in expected["families"]:
        b = family["B"]
        before = sum(row["B"] == b for row in rows)
        removed = sum(row["B"] == b for row in paid)
        after = sum(row["B"] == b for row in kept)
        terminals = sum(row["B"] == b and row["terminal"] for row in kept)
        if before != family["pending_subtrees"] or before != removed+after:
            raise ValueError("independent family conservation failed")
        family.update({
            "closed_ear_core_capacity_whole_subtrees": removed,
            "pending_subtrees": after, "unresolved_terminal_subtrees": terminals,
            "family_exhausted": after == 0,
        })
        conservation.append({
            "B": b, "actual_source_subtrees": before,
            "strict_closed_ear_whole_subtrees": removed, "retained_subtrees": after,
            "all_raw_terminals_retained": terminals,
        })
    if filtered != expected:
        raise ValueError("filtered frontier omitted, invented, changed or reordered an unpaid sibling")
    if [row for row in kept if row["terminal"]] != [row for row in rows if row["terminal"]]:
        raise ValueError("candidate or competitor raw terminal changed")
    if (
        len(rows) != 11183 or len(paid) != 643 or len(kept) != 10540
        or dict(Counter(str(row["B"]) for row in paid)) != {"16": 3, "17": 640}
        or cases_checked != 673 or m_checked != 646
        or [item["retained_subtrees"] for item in conservation] != [296, 1224, 4539, 4481]
        or min(F(4, 5)-2*U, 1-4*U, F(3, 4)-F(4, 5)**2, F(7, 4)**2-3) <= 0
    ):
        raise ValueError("independent full-source count, case cover or exact strict margin changed")
    return {
        "entire_source_prefixes_independently_scanned": len(rows),
        "strict_whole_ear_prefixes": len(paid),
        "retained_unpaid_source_prefixes": len(kept),
        "original_physical_count_cases": m_checked,
        "original_physical_count_and_all_shadow_label_cases": cases_checked,
        "independent_family_conservation": conservation,
        "all_raw_terminals_and_unpaid_siblings_retained_identically": True,
        "all_original_source_prefixes_prefix_free": True,
        "continuous_geometry_not_inferred_from_finite_accounting": True,
        "candidate_whole_roots_removed": 0,
    }


def current_gate(current, parent, result, layer):
    families = deepcopy(parent["Rstar_conditional_frontier_families"])
    for family, counts in zip(families, result["independent_family_conservation"]):
        if family["B"] != counts["B"]:
            raise ValueError("closed-ear current reordered its actual families")
        family.update({
            "closed_ear_core_capacity_whole_subtrees": counts["strict_closed_ear_whole_subtrees"],
            "pending_subtrees": counts["retained_subtrees"],
            "unresolved_terminal_subtrees": counts["all_raw_terminals_retained"],
            "family_exhausted": counts["retained_subtrees"] == 0,
        })
    if (
        current["schema"] != CURRENT_SCHEMA
        or current["current_bound_bytes_rechecked"] is not True
        or current["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or current["closed_ear_actual_published_and_complete_current_semantic_replays_equal"] is not True
        or current["closed_ear_full_current_semantic_exit_code"] != 0
        or current["independent_exact_closed_ear_source_accounting"] != result
        or current["closed_ear_actual_prior_candidate_layer_identity"] != layer
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or current["closed_ear_candidate_whole_roots_removed"] != 0
        or current["Rstar_conditional_frontier_pending_subtrees"] != 10540
        or current["Rstar_conditional_frontier_families"] != families
        or current["closed_ear_new_strict_whole_source_prefixes"] != 643
        or current["closed_ear_source_conditional_pending_subtrees"] != 11183
        or current["radius_scope"] != SCOPE
        or current["r_strict_interval"] != parent["r_strict_interval"]
        or current["original_U_current_pending_subtrees_unchanged"] != 3922
        or current["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or current["all_siblings_unresolved_terminals_OPEN_boundaries_and_old_proofs_retained"] is not True
        or current["joined_closed_full_type_codes_in_these_two_catalogues"] != 87
        or current["all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"] != 215
        or any(current[field] != parent[field] for field in (
            "all_current_competitor_terminal_obligations_explicitly_retained",
            "current_candidate_type_paths", "known_candidate_unique_complete_34_face_terminal"))
        or any(current[name] is not False for name in (
            "inherited_source_is_unconditional_at_U", "unrestricted_reduction_final_joint_acceptance",
            "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or any(current["files"].get(text) != digest for text, digest in parent["files"].items())
    ):
        raise ValueError("closed-ear current changed source scope, candidate history or old proof inventory")
