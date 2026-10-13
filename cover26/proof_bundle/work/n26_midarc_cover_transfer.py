"""Complete original-prefix semantics for the NEW680 midarc source supplement.

Uses actual SIX-filtered source rows; never restores the11183 old frontier.
Independent whole-prefix accounting is in a distinct module.
"""

from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations

from audit_prefix_origin import OriginReference
import n26_force as force
import n26_closed_ear_cover_transfer as original
import n26_midarc_filled_patches as rule
import n26_midarc_source_accounting as independent
import n26_six_target_filled_ears as family


MODE = independent.MODE
U = rule.U


def lemma_gate(certificates, proofs):
    if set(proofs) != {"cap", "generic", "bridge", "ear", "midarc"}:
        raise ValueError("midarc supplement lacks every written continuous ingredient")
    if any(not isinstance(value, str) or len(value) != 64
           or any(char not in "0123456789abcdef" for char in value) for value in proofs.values()):
        raise ValueError("midarc continuous proof is not explicitly content bound")
    symbolic = original.lemma_gate(
        certificates, {key: value for key, value in proofs.items() if key != "midarc"},
    )
    targets = {str(k): rule.target_gate(k) for k in (3, 4, 5, 6)}
    if targets != independent.independent_targets():
        raise ValueError("independent exact midarc distance/half-angle/projection comparisons disagree")
    return symbolic, targets


def shadow_cases(row, patch):
    b = row["B"]
    outside = set(range(b, 26))-set(patch["actual_enclosed_nonowner_labels"])
    required = rule.REQUIRED[patch["outer_cycle_length"]]
    result = []
    for m in range(b+9, 27):
        counts = Counter()
        for shadows in combinations(range(b, 26), 26-m):
            available = len(outside-set(shadows))
            if available >= required:
                raise ValueError("a shadow-placement case can supply the midarc outside targets")
            counts[available] += 1
        result.append({
            "original_irredundant_physical_disks": m, "shadow_labels_count": 26-m,
            "all_original_label_placements_checked": sum(counts.values()),
            "placements_by_original_nonowners_available_outside_patch": {
                str(value): counts[value] for value in sorted(counts)
            },
        })
    return result


def partition(source, constants, certificates, proofs):
    family.family_gate(constants)
    symbolic, targets = lemma_gate(certificates, proofs)
    if (
        source["schema"] != independent.SOURCE_SCHEMA or source["N"] != 26
        or source["radius_scope"] != independent.SCOPE
        or source["inherited_source_is_unconditional_at_U"] is not False
        or not 0 < F(source["radius_upper"]) < U or len(source["pending_states"]) != 5637
    ):
        raise ValueError("midarc transfer requires the actual SIX-filtered conditional source")
    references = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                  for b in (14, 15, 16, 17)}
    for reference in references.values():
        reference.children = lru_cache(None)(reference.children)
    seen, kept, ledger, case_count = set(), [], [], 0
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("midarc transfer duplicate actual source prefix")
        seen.add(key)
        reference = references[row["B"]]
        state = reference.resolve(key[1])
        if {"B": row["B"], **reference.entry(key[1], state, reference.children(state))} != row:
            raise ValueError("midarc ENTIRE actual ORIGINAL source-prefix reconstruction differs")
        first, second = rule.patches(row), rule.patches(row, independent_locator=True)
        if first != second:
            raise ValueError("midarc distinct full-source locator/topology gates disagree")
        if not first:
            kept.append(row)
            continue
        if row["terminal"]:
            raise ValueError("midarc transfer paid a raw complete candidate/competitor terminal")
        selected = max(first, key=lambda patch: (
            patch["required_DISTINCT_ORIGINAL_outside_nonowners"]
            - patch["maximum_all_original_nonowner_slots_outside"], -patch["outer_cycle_length"],
        ))
        cases = shadow_cases(row, selected)
        if cases != independent.independent_original_cases(row, selected):
            raise ValueError("midarc shadow-subset and ORIGINAL-subset enumerations disagree")
        count = sum(item["all_original_label_placements_checked"] for item in cases)
        case_count += count
        ledger.append({
            "mode": MODE, "source_index": index, "B": row["B"], "prefix": row["prefix"],
            "actual_entire_source_state": row, "all_qualifying_filled_patches": first,
            "selected_strongest_filled_patch": selected,
            "all_original_physical_count_and_shadow_case_distributions": cases,
            "original_count_and_shadow_cases_checked": count,
            "continuous_proof_sha256": proofs, "exact_midarc_core_target_identities": targets,
            "outside_budget_INCLUDES_introduced_outside_vertices_AND_future_labels": True,
            "midpoint_of_actual_short_anchor_arc_NOT_first_anchor_frame": True,
            "whole_source_angular_domain_and_ALL_descendant_continuations_excluded": True,
            "original_owner_frame_NOT_26_distinct_shadow_Voronoi_cells": True,
            "exclusion_uses_actual_core_coverage_AND_embedded_filled_patch_NOT_only_weak_rods": True,
            "formal_payment_requires_actual_source_geometry_publication_current_AND_independent_final": True,
        })
    if any((b, prefix[:size]) in seen for b, prefix in seen for size in range(len(prefix))):
        raise ValueError("midarc source has overlapping ancestor/descendant ownership")
    if [row for row in kept if row["terminal"]] != [
        row for row in source["pending_states"] if row["terminal"]
    ]:
        raise ValueError("midarc transfer lost a complete raw terminal")
    frontier = deepcopy(source)
    frontier["schema"] = independent.FRONTIER_SCHEMA
    frontier["pending_states"] = kept
    conservation = []
    for record in frontier["families"]:
        b = record["B"]
        incoming = sum(row["B"] == b for row in source["pending_states"])
        removed = sum(row["B"] == b for row in ledger)
        outgoing = sum(row["B"] == b for row in kept)
        terminals = sum(row["B"] == b and row["terminal"] for row in kept)
        if incoming != record["pending_subtrees"] or incoming != removed+outgoing:
            raise ValueError("midarc exact family conservation failed")
        record.update({
            "midarc_filled_patch_NEW_whole_subtrees": removed, "pending_subtrees": outgoing,
            "unresolved_terminal_subtrees": terminals, "family_exhausted": outgoing == 0,
        })
        conservation.append({
            "B": b, "actual_SIX_filtered_source_subtrees": incoming,
            "strict_NEW_midarc_whole_subtrees": removed, "retained_subtrees": outgoing,
            "all_raw_terminals_retained": terminals,
        })
    if (
        len(ledger) != 680 or len(kept) != 4957 or case_count != 9172
        or [row["pending_subtrees"] for row in frontier["families"]] != [296, 647, 2164, 1850]
    ):
        raise ValueError("midarc actual remaining-source totals differ from independently checked mathematics")
    return frontier, ledger, {
        "entire_actual_ORIGINAL_SIX_filtered_source_prefixes_reconstructed": 5637,
        "strict_NEW_midarc_whole_prefixes": len(ledger),
        "new_midarc_boundary_family_counts": dict(Counter(str(row["B"]) for row in ledger)),
        "all_original_physical_count_AND_shadow_label_cases_checked": case_count,
        "distinct_patch_locators_AND_original_vs_shadow_set_enumerations_agreed": True,
        "all_raw_complete_candidate_and_competitor_terminals_retained_identically": True,
        "prefix_free_entire_source_and_unpaid_sibling_partition_checked": True,
        "old5546_SIX_whole_prefixes_NOT_repaid": True,
        "family_conservation": conservation,
        "fresh_universal_algebra_ingredients": symbolic,
        "fresh_independent_exact_midarc_core_target_identities": targets,
        "written_continuous_cover_embedding_and_MIDARC_proofs_bound_NOT_inferred_from_tests": True,
    }
