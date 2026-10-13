"""Experimental exact weighted Taylor-segment Hessian minorants.

This supplies arithmetic only, not source/model replay or geometric payments.
Existing hull/owned acceptance modules are left unchanged.
"""

from fractions import Fraction as F

import n26_signed_hull_energy_minorant as hull


def integrated_minorant(kernel, matrix, reference, lower, upper, arcs, parts):
    if type(parts) is not int or not 1 <= parts <= 256:
        raise ValueError("invalid integrated Taylor partition count")
    if (kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not True
            or kernel["B"] != 16 or kernel["vertices"] != 62
            or len(kernel["weights"]) != 92):
        raise ValueError("integrated hull changed the original 92-rod model")
    ref, lo, hi, _, _ = hull.hull_gate(reference, lower, upper, matrix)
    n = kernel["B"] - 1
    combined = [[F(0) for _ in range(n)] for _ in range(n)]
    total_weight, intervals = F(0), []
    for index in range(parts):
        left, right = F(index, parts), F(index + 1, parts)
        # Normalized integral of 2(1-t) over this closed Taylor strip.
        weight = 2 * (right - left) - (right**2 - left**2)
        if weight <= 0:
            raise ValueError("nonpositive integrated Taylor strip weight")
        strip_lo, strip_hi = [], []
        for r, a, c in zip(ref[1:], lo[1:], hi[1:]):
            endpoints = [r + t * (x - r) for t in (left, right) for x in (a, c)]
            strip_lo.append(min(endpoints))
            strip_hi.append(max(endpoints))
        minorant = hull.quadratic.hessian_minorant(
            kernel, matrix, strip_lo, strip_hi, arcs)
        for i in range(n):
            for j in range(n):
                combined[i][j] += weight * minorant[i][j]
        total_weight += weight
        intervals.append({
            "t_closed_lower": str(left), "t_closed_upper": str(right),
            "normalized_Taylor_weight": str(weight),
            "closed_coordinate_lower": list(map(str, strip_lo)),
            "closed_coordinate_upper": list(map(str, strip_hi)),
        })
    if total_weight != 1 or any(
            combined[i][j] != combined[j][i] for i in range(n) for j in range(n)):
        raise AssertionError("integrated Taylor weights or exact symmetry changed")
    return combined, {
        "all_closed_Taylor_strips_and_shared_t_endpoints_covered": True,
        "exact_normalized_integral_weights_sum": str(total_weight),
        "parts": parts, "closed_Taylor_strips": intervals,
        "necessary_difference_polytope_convexity_used_for_every_segment_point": True,
        "matrix_minorant_is_twice_the_Taylor_integral": True,
    }


def gate(kernel, matrix, reference, lower, upper, eta, arcs, parts):
    diagonal = list(map(F, eta))
    n = kernel["B"] - 1
    if len(diagonal) != n or any(abs(value) > 10**60 for value in diagonal):
        raise ValueError("invalid integrated signed-curvature diagonal")
    combined, partition = integrated_minorant(
        kernel, matrix, reference, lower, upper, arcs, parts)
    # Every strip has symmetric entry error <1/grid. Positive normalized
    # weights sum exactly to 1, so the SAME n/grid operator error is charged.
    tested = [[value + (diagonal[i] - F(n, hull.quadratic.ROUND_GRID)
                        if i == j else 0)
               for j, value in enumerate(row)]
              for i, row in enumerate(combined)]
    pivots = hull.quadratic.positive_ldl(tested)
    return {
        **partition, "signed_eta": list(map(str, diagonal)),
        "exact_positive_LDL_and_full_rational_reconstruction_checked": True,
        "weighted_symmetric_rounding_operator_error_charged": str(
            F(n, hull.quadratic.ROUND_GRID)),
        "exact_LDL_minimum_pivot": str(min(pivots)),
        "verified": False, "new_geometric_payments": 0,
        "full_actual_latest_source_model_ownership_gate_still_required": True,
    }
