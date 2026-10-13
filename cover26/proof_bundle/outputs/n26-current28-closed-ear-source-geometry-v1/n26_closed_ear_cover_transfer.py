"""Pure exact source partition for the new closed-ear geometric rule.

The continuous proof is explicit in its bound manuscript, not supplied by
synthetic receipt shapes or a finite geometry example.
"""

from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations

from audit_prefix_origin import OriginReference
import n26_force as force
import n26_embedded_dual_bridge_algebra as bridge
import n26_unit_cap_universal_identities as cap
import n26_generic_position_universal_polynomials as generic
from audit_n26_closed_ear_core_capacity import ear_patch
from test_n26_closed_ear_core_capacity import independent_patch


MODE = "N26-closed-ear-core-capacity-original-owner-corner-shadow-v1"
U = F(234701, 1000000)


def original_count_cases(b, constants):
    if (type(b) is not int or b not in (14, 15, 16, 17)
            or constants["N"] != 26 or F(constants["radius_upper"]) != U
            or constants["minimum_interior_cells"] != 9
            or constants["minimum_boundary_cells"] != 14
            or constants["maximum_boundary_cells"] != 17
            or constants["external_n8_theorem_assumed"] is not True
            or constants["n8_reproved_here"] is not False
            or constants["families"] != [[14, 12], [15, 11], [16, 10], [17, 9]]):
        raise ValueError("closed-ear bridge changed the explicit ORIGINAL-owner family theorem")
    return list(range(b+9, 27))


def shadow_placement_cases(row, constants):
    b, introduced = row["B"], row["next"]
    cases = []
    for original_disks in original_count_cases(b, constants):
        for shadow_tuple in combinations(range(b, 26), 26-original_disks):
            shadows = set(shadow_tuple)
            original_nonowners = set(range(b, 26))-shadows
            inside = original_nonowners.intersection(range(b, introduced))
            possible_outside = original_nonowners.intersection(range(introduced, 26))
            if (len(original_nonowners) != original_disks-b
                    or len(possible_outside) > 26-introduced
                    or len(possible_outside) >= 4):
                raise ValueError("closed ear fails an ORIGINAL nonowner/shadow-placement case")
            cases.append({
                "original_irredundant_physical_disks": original_disks,
                "shadow_labels": sorted(shadows),
                "retained_original_nonowner_labels_inside_filled_ear": sorted(inside),
                "retained_original_nonowner_labels_not_yet_introduced": sorted(possible_outside),
                "maximum_original_nonowners_available_for_four_core_points": len(possible_outside),
                "four_DISTINCT_ORIGINAL_nonowners_required": 4,
            })
    if not cases:
        raise ValueError("no original-cover cardinality case")
    return cases


def lemma_gate(certificates, proofs):
    if set(certificates) != {"cap", "generic", "bridge"} or set(proofs) != {
            "cap", "generic", "bridge", "ear"}:
        raise ValueError("missing a universal geometric ingredient")
    result = {
        "cap": cap.gate(certificates["cap"]),
        "generic": generic.gate(certificates["generic"]),
        "bridge": bridge.gate(certificates["bridge"]),
    }
    if (result["cap"]["universal_polynomial_identities_exactly_checked"] != 8
            or result["bridge"]["universal_exact_empty_circle_stellar_identities_checked"] != 12
            or any(not text or len(text) != 64 or any(c not in "0123456789abcdef" for c in text)
                   for text in proofs.values())):
        raise ValueError("universal geometry algebra/proof binding changed")
    h, core = F(4, 5)-U, 1-2*U
    if (not U < F(1, 4) or not h > U or not core > 2*U
            or not F(3) < F(7, 4)**2 or not F(3, 4) > F(4, 5)**2):
        raise ValueError("closed-ear/core strict whole-domain inequalities failed")
    return result


def partition(source, constants, certificates, proofs):
    symbolic = lemma_gate(certificates, proofs)
    if (source["N"] != 26 or source["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or source["inherited_source_is_unconditional_at_U"] is not False
            or not 0 < F(source["radius_upper"]) < U):
        raise ValueError("closed-ear source changed its inherited conditional radius")
    rows = source["pending_states"]
    refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D) for b in (14, 15, 16, 17)}
    for reference in refs.values():
        reference.children = lru_cache(None)(reference.children)
    seen, retained, ledger = set(), [], []
    for index, row in enumerate(rows):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("duplicate actual source-prefix ownership")
        seen.add(key)
        ref = refs[row["B"]]
        state = ref.resolve(key[1])
        if {"B": row["B"], **ref.entry(key[1], state, ref.children(state))} != row:
            raise ValueError("ENTIRE actual source contains a mismatched original prefix")
        patch, other = ear_patch(row), independent_patch(row)
        if patch != other:
            raise ValueError("independent full closed-patch methods disagree")
        if patch is None:
            retained.append(row)
            continue
        if row["terminal"]:
            raise ValueError("a complete candidate/competitor terminal was relabeled as an ear")
        cases = shadow_placement_cases(row, constants)
        ledger.append({
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
        })
    # A bound source frontier is prefix-free. Check this explicitly, including
    # every retained sibling, not only selected exclusions.
    for b, prefix in seen:
        if any((b, prefix[:length]) in seen for length in range(len(prefix))):
            raise ValueError("source states overlap by an ancestor/descendant prefix")
    old_terminal = [row for row in rows if row["terminal"]]
    if [row for row in retained if row["terminal"]] != old_terminal:
        raise ValueError("a raw candidate or competitor terminal disappeared")
    frontier = deepcopy(source)
    frontier["schema"] = "N26-closed-ear-core-capacity-filtered-conditional-frontier-v1"
    frontier["pending_states"] = retained
    conservation = []
    for family in frontier["families"]:
        b = family["B"]
        before = sum(row["B"] == b for row in rows)
        paid = sum(row["B"] == b for row in ledger)
        after = sum(row["B"] == b for row in retained)
        terminals = sum(row["B"] == b and row["terminal"] for row in retained)
        if before != family["pending_subtrees"] or before-paid != after:
            raise ValueError("ear source/family conservation failed")
        family["closed_ear_core_capacity_whole_subtrees"] = paid
        family["pending_subtrees"] = after
        family["unresolved_terminal_subtrees"] = terminals
        family["family_exhausted"] = after == 0
        conservation.append({"B": b, "actual_source_subtrees": before,
                             "strict_closed_ear_whole_subtrees": paid, "retained_subtrees": after,
                             "all_raw_terminals_retained": terminals})
    return frontier, ledger, {
        "entire_actual_source_prefixes_reconstructed": len(rows),
        "closed_ear_whole_prefixes": len(ledger),
        "closed_ear_boundary_family_counts": dict(Counter(str(row["B"]) for row in ledger)),
        "original_physical_count_cases_checked": sum(len(original_count_cases(row["B"], constants)) for row in ledger),
        "original_physical_count_AND_all_shadow_label_placement_cases_checked": sum(
            len(row["original_physical_count_and_all_shadow_label_placement_cases"]) for row in ledger),
        "all_raw_complete_terminals_retained_identically": True,
        "prefix_free_whole_source_partition_checked": True,
        "family_conservation": conservation,
        "actual_universal_algebra_results": symbolic,
        "written_continuous_cover_dual_star_and_ear_proofs_bound_NOT_inferred_from_code": True,
    }
