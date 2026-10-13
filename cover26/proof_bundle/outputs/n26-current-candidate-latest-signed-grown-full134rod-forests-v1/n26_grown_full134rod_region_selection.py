"""Select only freshly reconstructed grown regions, never cached payments.

Pure model/energy arithmetic. Caller must separately bind actual reports,
current source/history and newest forest; no diagnostic producer is imported.
"""

from copy import deepcopy
from fractions import Fraction as F

import n26_mixed_full134rod_support_forest as mixed


SCHEMA = "N26-unaccepted-actual-source-root-clipped-grown-full134rod-regions-v1"
WIDTHS = tuple(map(F, ("1/1000", "1/500", "1/200", "1/100", "1/50")))


def select(original, arcs, row, full_supports, record):
    model = mixed.model_gate(original)
    kernels = mixed.full_support_gate(model, full_supports)
    if (record["schema"] != SCHEMA or record["actual_source_closed_box"] != row
            or record["source_OPEN_index"] != row["index"]
            or record["NEW_distinct_full134rod_edges"] != model["edges"]
            or record["checked_root_half_widths"] != list(map(str, WIDTHS))
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["successful_regions_NEED_fresh_latest_OPEN_intersections_and_all_remainders"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True
            or record["nested_regions_are_NOT_disjoint_paid_leaves_or_a_latest_forest_cover"] is not True):
        raise ValueError("grown region DATA was promoted to a newest forest or geometric payment")
    contractor = mixed.old.prior.prior.tighten
    independent = mixed.old.prior.prior.independently_contract
    root = independent(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    used, selected, audit = set(), [], []
    for item in record["results"]:
        matching = [
            index for index, support in enumerate(full_supports)
            if support["kernel_certificate"] == item["NEW_full134rod_stress_kernel_certificate"]
            and support["suggestion_point_turns"] == item["actual_feasible_reference_turns"]
        ]
        if len(matching) != 1 or matching[0] in used:
            raise ValueError("grown region DATA changed or repeated its actual distinct support")
        index = matching[0]
        used.add(index)
        reference = list(map(F, item["actual_feasible_reference_turns"]))
        if len(reference) != 15 or len(item["trials"]) != len(WIDTHS):
            raise ValueError("grown region DATA lost its reference or requested closed regions")
        candidates, previous = [], None
        for expected_width, trial in zip(WIDTHS, item["trials"]):
            if (trial["requested_root_closed_half_width"] != str(expected_width)
                    or trial["old_checked_v7_leaf_boundary_NOT_used_to_clip_this_region"] is not True):
                raise ValueError("grown region selection used old-leaf clipping or changed widths")
            lower = [max(F(a), t-expected_width) for a, t in zip(row["sharp_lower"], reference)]
            upper = [min(F(b), t+expected_width) for b, t in zip(row["sharp_upper"], reference)]
            actual = independent(original["matrix"], lower, upper)
            if (actual is None or actual != contractor(original["matrix"], lower, upper)
                    or actual != (
                        list(map(F, trial["actual_source_root_clipped_closed_lower"])),
                        list(map(F, trial["actual_source_root_clipped_closed_upper"])))
                    or type(trial["region_equals_entire_actual_source_root"]) is not bool
                    or trial["region_equals_entire_actual_source_root"] != (actual == root)):
                raise ValueError("grown region selection changed the entire actual closed region")
            mixed.correlated.full.hull.quadratic.reference_gate(
                reference, *actual, original["matrix"])
            if previous is not None and any(not a <= x <= y <= b
                                            for a, b, x, y in zip(*actual, *previous)):
                raise ValueError("grown region selection lost a nested predecessor")
            previous = actual
            certificate, result = trial["NEW_correlated_certificate"], trial["NEW_correlated_result"]
            strict = False
            if certificate is not None:
                fresh = mixed.correlated.bound(
                    kernels[index], original["matrix"], *actual, certificate, original["radius"], arcs)
                if fresh != result:
                    raise ValueError("grown region cached result failed fresh exact reconstruction")
                strict = fresh["arithmetic_strict_target_test_passed"]
            elif result is not None:
                raise ValueError("grown region result has no actual full134rod certificate")
            if (type(trial["fresh_exact_strict_closed_region"]) is not bool
                    or trial["fresh_exact_strict_closed_region"] != strict):
                raise ValueError("grown region selection changed actual strictness")
            audit.append({
                "full_support_index": index, "half_width": str(expected_width),
                "fresh_strict": strict, "whole_actual_source_root": actual == root,
            })
            if strict:
                candidates.append((expected_width, {
                    "lower": list(map(str, actual[0])), "upper": list(map(str, actual[1])),
                    "full_support_index": index, "certificate": deepcopy(certificate),
                }))
        if candidates:
            width, region = max(candidates, key=lambda pair: pair[0])
            selected.append(region)
    if used != set(range(len(full_supports))):
        raise ValueError("grown region DATA omitted a distinct checked support origin")
    return selected, audit
