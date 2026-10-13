"""Complete source transfer of the written six-target filled-ear rule.

Whole geometric prefixes are excluded, never merely sampled angle points.
Real geometry/current/final acceptance remains separate from this pure replay.
"""

from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache

from audit_prefix_origin import OriginReference
import n26_force as force
import n26_closed_ear_cover_transfer as original
import n26_six_target_filled_ears as rule
import test_six_target_filled_boundary_ears as independent


MODE = "N26-six-core-target-filled-original-owner-ear-v1"
FRONTIER_SCHEMA = "N26-six-core-target-filled-ear-filtered-conditional-frontier-v1"
U = rule.U


def lemma_gate(certificates, proofs):
    if set(proofs) != {"cap", "generic", "bridge", "ear", "six"}:
        raise ValueError("six-target source lacks every written continuous proof ingredient")
    symbolic = original.lemma_gate(certificates, {key: value for key, value in proofs.items() if key != "six"})
    if not isinstance(proofs["six"], str) or len(proofs["six"]) != 64 or any(
        char not in "0123456789abcdef" for char in proofs["six"]
    ):
        raise ValueError("six-target continuous proof is not explicitly content bound")
    target = rule.target_gate()
    # Fresh independent scalar arithmetic rather than a stored target result.
    radius = 1-2*U
    points = [(F(0), F(0)), (radius/2, radius/2), (radius/2, -radius/2),
              (-radius/2, radius/2), (-radius/2, -radius/2), (-radius, F(0))]
    from itertools import combinations
    squared = [(a[0]-b[0])**2+3*(a[1]-b[1])**2 for a, b in combinations(points, 2)]
    if (
        min(squared) != radius**2 or min(squared) <= 4*U**2
        or F(4, 5)-U-max(x for x, y in points) != F(3, 10)
        or F(3, 10) <= U
        or target["exact_minimum_squared_pair_distance"] != str(min(squared))
    ):
        raise ValueError("six-target independent universal distance/projection calculation differs")
    return symbolic, target


def partition(source, constants, certificates, proofs):
    symbolic, target = lemma_gate(certificates, proofs)
    rule.family_gate(constants)
    if (
        source["N"] != 26 or source["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
        or source["inherited_source_is_unconditional_at_U"] is not False
        or not 0 < F(source["radius_upper"]) < U
        or [family["B"] for family in source["families"]] != [14, 15, 16, 17]
    ):
        raise ValueError("six-target source changed its conditional radius or original owner families")
    references = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                  for b in (14, 15, 16, 17)}
    for reference in references.values():
        reference.children = lru_cache(None)(reference.children)
    seen, kept, ledger, case_count = set(), [], [], 0
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("duplicate actual whole-source prefix ownership")
        seen.add(key)
        reference = references[row["B"]]
        state = reference.resolve(key[1])
        if {"B": row["B"], **reference.entry(key[1], state, reference.children(state))} != row:
            raise ValueError("six-target ENTIRE original source-prefix replay differs")
        first, second = rule.patches(row), independent.independent_patches(row)
        if first != second:
            raise ValueError("distinct entire-source filled-patch scans disagree")
        if not first:
            kept.append(row)
            continue
        if row["terminal"]:
            raise ValueError("a complete candidate or competitor was relabeled as an impossible ear")
        selected = max(first, key=lambda patch: len(patch["actual_enclosed_nonowner_labels"]))
        cases = rule.shadow_case_distributions(row, selected)
        if cases != independent.independent_original_cases(row, selected):
            raise ValueError("independent original-subset and shadow-subset enumeration disagree")
        count = sum(item["all_shadow_label_placements_checked"] for item in cases)
        case_count += count
        ledger.append({
            "mode": MODE, "source_index": index, "B": row["B"], "prefix": row["prefix"],
            "actual_entire_source_state": row,
            "all_qualifying_filled_patches": first,
            "selected_strongest_filled_patch": selected,
            "all_original_physical_count_and_shadow_case_distributions": cases,
            "original_count_and_shadow_cases_checked": count,
            "continuous_proof_sha256": proofs,
            "exact_six_core_target_identities": target,
            "outside_budget_INCLUDES_introduced_outside_vertices_AND_future_labels": True,
            "original_owner_frame_NOT_26_distinct_shadow_Voronoi_cells": True,
            "whole_source_angular_domain_and_ALL_descendant_continuations_excluded": True,
            "exclusion_uses_actual_core_coverage_AND_embedded_filled_patch_NOT_only_weak_rods": True,
            "formal_payment_requires_actual_source_geometry_publication_current_AND_independent_final": True,
        })
    if any((b, prefix[:length]) in seen for b, prefix in seen for length in range(len(prefix))):
        raise ValueError("source frontier overlaps an ancestor and descendant prefix")
    if [row for row in kept if row["terminal"]] != [
        row for row in source["pending_states"] if row["terminal"]
    ]:
        raise ValueError("a raw complete candidate/competitor terminal disappeared")
    frontier = deepcopy(source)
    frontier["schema"] = FRONTIER_SCHEMA
    frontier["pending_states"] = kept
    conservation = []
    for family in frontier["families"]:
        b = family["B"]
        incoming = sum(row["B"] == b for row in source["pending_states"])
        removed = sum(row["B"] == b for row in ledger)
        outgoing = sum(row["B"] == b for row in kept)
        terminals = sum(row["B"] == b and row["terminal"] for row in kept)
        if incoming != family["pending_subtrees"] or incoming != removed+outgoing:
            raise ValueError("six-target exact source/family conservation failed")
        family.update({
            "six_core_target_filled_ear_whole_subtrees": removed,
            "pending_subtrees": outgoing, "unresolved_terminal_subtrees": terminals,
            "family_exhausted": outgoing == 0,
        })
        conservation.append({
            "B": b, "actual_source_subtrees": incoming,
            "strict_six_target_whole_subtrees": removed, "retained_subtrees": outgoing,
            "all_raw_terminals_retained": terminals,
        })
    if (
        len(source["pending_states"]) != 11183 or len(ledger) != 5546
        or len(kept) != 5637 or case_count != 58916
        or [family["pending_subtrees"] for family in frontier["families"]] != [296, 694, 2703, 1944]
    ):
        raise ValueError("six-target actual source/case/family totals differ from independent mathematics")
    return frontier, ledger, {
        "entire_actual_original_source_prefixes_reconstructed": len(source["pending_states"]),
        "six_target_strict_whole_prefixes": len(ledger),
        "six_target_boundary_family_counts": dict(Counter(str(row["B"]) for row in ledger)),
        "all_original_physical_count_AND_shadow_label_cases_checked": case_count,
        "distinct_patch_locators_AND_original_vs_shadow_set_enumerations_agreed": True,
        "all_raw_complete_candidate_and_competitor_terminals_retained_identically": True,
        "prefix_free_entire_source_and_unpaid_sibling_partition_checked": True,
        "family_conservation": conservation,
        "fresh_universal_algebra_ingredients": symbolic,
        "fresh_independent_exact_six_core_target_identities": target,
        "written_continuous_cover_embedding_shadow_AND_six_target_proofs_bound_NOT_inferred_from_tests": True,
    }
