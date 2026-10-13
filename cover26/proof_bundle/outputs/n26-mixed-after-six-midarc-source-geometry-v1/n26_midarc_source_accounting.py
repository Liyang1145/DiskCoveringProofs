"""Independent exact accounting for NEW680 on the actual SIX-filtered source.

No producer partition helper is called. Target arithmetic is written here
independently, patches use the dual/link locator, and ORIGINAL subsets are
enumerated rather than producer shadow subsets. These are pure checks,
not completed source geometry/current/final acceptance.
"""

from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations

import n26_midarc_filled_patches as rule
import n26_six_target_filled_ears as original_family


MODE = "N26-midarc-seven-six-five-core-target-filled-original-owner-patch-v1"
SOURCE_SCHEMA = "N26-six-core-target-filled-ear-filtered-conditional-frontier-v1"
FRONTIER_SCHEMA = "N26-midarc-filled-patch-filtered-conditional-frontier-v1"
INPUT_SCHEMA = "N26-actual-mixed-after-SIX-midarc-source-geometry-input-v1"
ACCEPTANCE_SCHEMA = "N26-actual-whole-SIX-filtered-source-midarc-geometry-acceptance-v1"
CHECKER = "verify_midarc_source_geometry.py"
SCOPE = "at-most-same-root-Rstar-not-original-U"
PARENT_SCHEMA = "N26-complete-current-chain-with-mixed-curvature-root-covers-audit-v1"
PARENT_FINAL_SCHEMA = "N26-independent-mixed-after-six-current-final-rehash-v1"
U = F(234701, 1000000)
PROOF_KEYS = {"cap", "generic", "bridge", "ear", "midarc"}
GLOBAL_FALSE = (
    "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started",
)


def parent_gate(parent, final, digest):
    if (
        parent["schema"] != PARENT_SCHEMA or final["schema"] != PARENT_FINAL_SCHEMA
        or final["current_audit_sha256"] != digest
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(parent["files"])
        or parent["current_bound_bytes_rechecked"] is not True
        or parent["prior_completed_full_chain_semantic_replay_still_bound"] is not True
        or parent["mixed_after_six_actual_completed_parent_pair_bound"] is not True
        or final["actual_completed_SIX_parent_pair_AND_identical_filtered_frontier_bound"] is not True
        or final["actual_NEW_current_executor_AND_tested_SIX_identity_adapter_bound"] is not True
        or parent["mixed_curvature_actual_full_semantic_exit_code"] != 0
        or parent["mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here"] is not True
        or final["mixed_actual_own_acceptance_publication_and_current_semantic_replays_equal"] is not True
        or parent["all_newest_owned_histories_retained_identically"] is not True
        or final["all_uncovered_whole_roots_and_latest_partial_histories_retained"] is not True
        or parent["current_transport_frontier_unchanged_by_mixed_candidate_covers"] is not True
        or parent["candidate_angle_unresolved_closed_boxes"] != 16
        or final["candidate_angle_unresolved_closed_boxes"] != 16
        or parent["remaining_latest_partial_root_histories"] != 1
        or final["remaining_latest_partial_root_histories"] != 1
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or final["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or parent["Rstar_conditional_frontier_families"] != final["Rstar_conditional_frontier_families"]
        or [(row["B"], row["pending_subtrees"]) for row in parent["Rstar_conditional_frontier_families"]]
        != [(14, 296), (15, 694), (16, 2703), (17, 1944)]
        or parent["radius_scope"] != SCOPE or final["radius_scope"] != SCOPE
        or parent["r_strict_interval"] != final["r_strict_interval"]
        or parent["original_U_current_pending_subtrees_unchanged"] != 3922
        or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or final["original_LOCAL_unchanged"] != "7/800000"
        or parent["joined_closed_full_type_codes_in_these_two_catalogues"] != 87
        or parent["all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked"] != 215
        or final["retained_closed_full_type_codes"] != 87
        or final["retained_checked_proof_receipts"] != 215
        or any(record[field] is not False for record in (parent, final) for field in GLOBAL_FALSE)
    ):
        raise ValueError("midarc geometry requires the actual completed mixed-after-SIX 16-root current/final")


def independent_targets():
    r = 1-2*U
    if not (U < F(1, 4) and F(7, 4)**2 > 3 and 0 < F(1054, 625)**2 < 3):
        raise ValueError("independent midarc original-arc/half-angle comparisons fail")
    result = {}
    for k in (3, 4, 5, 6):
        if k == 3:
            points = [(F(0), F(0)), (F(0), r), (r/2, r/2),
                      (r/2, -r/2), (F(0), -r), (-r/2, -r/2), (-r/2, r/2)]
            x_weight, y_weight, cosine, xmax = 3, 1, F(24, 25), 7*r/8
            description = "sqrt3*x_coefficient,y"
        elif k == 4:
            points = [(F(0), F(0)), (r/2, r/2), (r/2, -r/2),
                      (-r/2, r/2), (-r/2, -r/2), (-r, F(0))]
            x_weight, y_weight, cosine, xmax = 1, 3, F(4, 5), r/2
            description = "x,sqrt3*y_coefficient"
        else:
            points = [(F(0), F(0)), (F(0), r), (-r/2, r/2),
                      (-r/2, -r/2), (F(0), -r)]
            x_weight, y_weight = 3, 1
            cosine, xmax = (F(7, 10) if k == 5 else F(1, 2)), F(0)
            description = "sqrt3*x_coefficient,y"
        pairs = [x_weight*(a[0]-b[0])**2+y_weight*(a[1]-b[1])**2
                 for a, b in combinations(points, 2)]
        margin = cosine-2*U-xmax
        if (
            min(pairs) != r*r or min(pairs) <= 4*U*U or margin <= 0
            or any(x_weight*x*x+y_weight*y*y > r*r for x, y in points)
            or (k == 4 and 4*cosine*cosine >= 3)
            or (k == 5 and 2*cosine*cosine >= 1)
        ):
            raise ValueError("independent universal midarc target comparison fails")
        result[str(k)] = {
            "consecutive_original_owners": k,
            "required_DISTINCT_ORIGINAL_outside_nonowners": len(points),
            "target_coordinate_description": description,
            "exact_target_coefficients": [[str(x), str(y)] for x, y in points],
            "exact_core_radius": str(r), "exact_cosine_rational_lower": str(cosine),
            "exact_minimum_squared_pair_distance": str(min(pairs)),
            "exact_squared_pair_margin_above_four_U_squared": str(min(pairs)-4*U*U),
            "exact_target_x_rational_upper": str(xmax),
            "exact_patch_to_target_horizontal_margin_above_U": str(margin),
            "written_continuous_midarc_and_embedding_proof_STILL_explicit": True,
        }
    return result


def independent_original_cases(row, patch):
    b = row["B"]
    outside = set(range(b, 26))-set(patch["actual_enclosed_nonowner_labels"])
    need = {3: 7, 4: 6, 5: 5, 6: 5}[patch["outer_cycle_length"]]
    result = []
    for m in range(b+9, 27):
        counts = Counter()
        for originals in combinations(range(b, 26), m-b):
            available = len(outside.intersection(originals))
            if available >= need:
                raise ValueError("an original-disk placement can supply all midarc outside targets")
            counts[available] += 1
        result.append({
            "original_irredundant_physical_disks": m, "shadow_labels_count": 26-m,
            "all_original_label_placements_checked": sum(counts.values()),
            "placements_by_original_nonowners_available_outside_patch": {
                str(value): counts[value] for value in sorted(counts)
            },
        })
    return result


def partition_gate(source, frontier, ledger, constants, proofs):
    original_family.family_gate(constants)
    targets = independent_targets()
    if (
        source["schema"] != SOURCE_SCHEMA or source["N"] != 26
        or source["radius_scope"] != SCOPE
        or source["inherited_source_is_unconditional_at_U"] is not False
        or not 0 < F(source["radius_upper"]) < U
        or len(source["pending_states"]) != 5637
        or [(row["B"], row["pending_subtrees"]) for row in source["families"]]
        != [(14, 296), (15, 694), (16, 2703), (17, 1944)]
        or set(proofs) != PROOF_KEYS
        or any(not isinstance(value, str) or len(value) != 64
               or any(char not in "0123456789abcdef" for char in value)
               for value in proofs.values())
    ):
        raise ValueError("midarc accounting replaced the actual SIX-filtered source/radius/proof scope")
    owned = {}
    for row in ledger:
        index = row["source_index"]
        if type(index) is not int or not 0 <= index < len(source["pending_states"]) or index in owned:
            raise ValueError("invalid or duplicate midarc whole source-prefix ownership")
        owned[index] = row
    seen, kept, expected_ledger, case_count = set(), [], [], 0
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("midarc source duplicate prefix")
        seen.add(key)
        patches = rule.patches(row, independent_locator=True)
        if not patches:
            if index in owned:
                raise ValueError("midarc paid a nonqualifying or unfilled prefix")
            kept.append(row)
            continue
        if row["terminal"] or index not in owned:
            raise ValueError("midarc paid a complete raw terminal or omitted a qualifying prefix")
        selected = max(patches, key=lambda patch: (
            patch["required_DISTINCT_ORIGINAL_outside_nonowners"]
            - patch["maximum_all_original_nonowner_slots_outside"], -patch["outer_cycle_length"],
        ))
        cases = independent_original_cases(row, selected)
        count = sum(item["all_original_label_placements_checked"] for item in cases)
        expected = {
            "mode": MODE, "source_index": index, "B": row["B"], "prefix": row["prefix"],
            "actual_entire_source_state": row, "all_qualifying_filled_patches": patches,
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
        }
        if owned[index] != expected:
            raise ValueError("midarc exact source state/patch/case/continuous proof receipt changed")
        expected_ledger.append(expected)
        case_count += count
    if ledger != expected_ledger:
        raise ValueError("midarc ledger has reordered or additional whole-prefix ownership")
    if any((b, prefix[:size]) in seen for b, prefix in seen for size in range(len(prefix))):
        raise ValueError("midarc source ancestor/descendant overlap")
    expected_frontier = deepcopy(source)
    expected_frontier["schema"] = FRONTIER_SCHEMA
    expected_frontier["pending_states"] = kept
    conservation = []
    for family in expected_frontier["families"]:
        b = family["B"]
        incoming = sum(row["B"] == b for row in source["pending_states"])
        paid = sum(row["B"] == b for row in ledger)
        outgoing = sum(row["B"] == b for row in kept)
        raw = sum(row["B"] == b and row["terminal"] for row in kept)
        if incoming != family["pending_subtrees"] or incoming != paid+outgoing:
            raise ValueError("independent midarc family conservation failed")
        family.update({
            "midarc_filled_patch_NEW_whole_subtrees": paid, "pending_subtrees": outgoing,
            "unresolved_terminal_subtrees": raw, "family_exhausted": outgoing == 0,
        })
        conservation.append({
            "B": b, "actual_SIX_filtered_source_subtrees": incoming,
            "strict_NEW_midarc_whole_subtrees": paid, "retained_subtrees": outgoing,
            "all_raw_terminals_retained": raw,
        })
    if (
        frontier != expected_frontier or len(ledger) != 680 or len(kept) != 4957
        or case_count != 9172
        or [row["pending_subtrees"] for row in expected_frontier["families"]] != [296, 647, 2164, 1850]
        or [row for row in kept if row["terminal"]]
        != [row for row in source["pending_states"] if row["terminal"]]
    ):
        raise ValueError("midarc full accounting lost an unpaid sibling/raw terminal or re-paid older SIX prefixes")
    return {
        "entire_actual_SIX_filtered_source_prefixes_independently_scanned": 5637,
        "strict_NEW_midarc_whole_prefixes": 680, "retained_unpaid_source_prefixes": 4957,
        "original_physical_count_and_all_shadow_cases": case_count,
        "independent_family_conservation": conservation,
        "independent_exact_midarc_core_target_identities": targets,
        "all_unpaid_siblings_and_raw_terminals_retained_identically": True,
        "old5546_SIX_payments_NOT_repaid": True, "candidate_whole_roots_removed": 0,
    }
