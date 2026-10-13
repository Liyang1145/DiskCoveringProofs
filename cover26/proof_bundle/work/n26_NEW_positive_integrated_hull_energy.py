"""Distinct integrated Taylor arithmetic for NEW positive original-rod weights.

The original fixed-kernel identity is never forged. Fresh exact ground
inverse, SAME original edges and NEW weight sum are checked before generic
Hessian arithmetic. No source/model/history acceptance or payment occurs.
"""

from fractions import Fraction as F
from math import isqrt

import n26_reweighted_candidate_energy as alternative
import n26_signed_hull_energy_minorant as hull


def kernel_gate(original_reference, support):
    if (not isinstance(support, dict)
            or set(support) != {"mode", "reference", "inverse", "suggestion_point_turns"}
            or support["mode"] != "NEW-POSITIVE-SUPPORT"):
        raise ValueError("NEW integrated support has unknown or missing explicit mode fields")
    kernel = alternative.kernel_gate(original_reference, support["reference"], support["inverse"])
    if (kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
            or kernel["alternative_positive_support_of_original_92_rods_NOT_original_fixed_weights"] is not True):
        raise ValueError("NEW integrated arithmetic forged the original fixed-weight kernel identity")
    return kernel


def minorant(kernel, matrix, reference, lower, upper, arcs, parts):
    if (type(parts) is not int or not 1 <= parts <= 256
            or kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
            or kernel.get("alternative_positive_support_of_original_92_rods_NOT_original_fixed_weights") is not True
            or kernel["B"] != 16 or kernel["vertices"] != 62 or len(kernel["weights"]) != 92):
        raise ValueError("NEW integrated arithmetic has invalid partitions or explicit positive-support identity")
    reference, lo, hi, _, _ = hull.hull_gate(reference, lower, upper, matrix)
    n, total, combined = kernel["B"]-1, F(0), [[F(0)]*15 for _ in range(15)]
    strips = []
    for index in range(parts):
        left, right = F(index, parts), F(index+1, parts)
        weight = 2*(right-left)-(right**2-left**2)
        if weight <= 0:
            raise ValueError("NEW integrated Taylor strip has a nonpositive exact normalized weight")
        strip_lo, strip_hi = [], []
        for r, a, b in zip(reference[1:], lo[1:], hi[1:]):
            values = [r+t*(x-r) for t in (left, right) for x in (a, b)]
            strip_lo.append(min(values))
            strip_hi.append(max(values))
        matrix_bound = hull.quadratic.hessian_minorant(kernel, matrix, strip_lo, strip_hi, arcs)
        for i in range(n):
            for j in range(n):
                combined[i][j] += weight*matrix_bound[i][j]
        total += weight
        strips.append({
            "t_closed_lower": str(left), "t_closed_upper": str(right),
            "normalized_Taylor_weight": str(weight),
            "closed_coordinate_lower": list(map(str, strip_lo)),
            "closed_coordinate_upper": list(map(str, strip_hi)),
        })
    if (total != 1 or any(combined[i][j] != combined[j][i] for i in range(n) for j in range(n))
            or strips[0]["t_closed_lower"] != "0" or strips[-1]["t_closed_upper"] != "1"
            or any(a["t_closed_upper"] != b["t_closed_lower"] for a, b in zip(strips, strips[1:]))):
        raise AssertionError("NEW integrated Taylor strips lost exact normalized coverage or symmetry")
    return combined, {
        "parts": parts, "closed_Taylor_strips": strips,
        "exact_normalized_integral_weights_sum": str(total),
        "all_closed_Taylor_strips_and_shared_t_endpoints_covered": True,
        "convex_necessary_difference_reference_hull_contains_every_segment_point": True,
        "NEW_weight_minorant_is_twice_the_exact_Taylor_integral": True,
    }


def bound(original_reference, support, matrix, lower, upper, certificate, radius, arcs):
    if (not isinstance(certificate, dict)
            or set(certificate) != {"reference_turns", "parts", "signed_eta", "difference_dual"}):
        raise ValueError("NEW integrated certificate has unknown or missing distinct mode fields")
    kernel = kernel_gate(original_reference, support)
    ref, lo, hi, _, _ = hull.hull_gate(certificate["reference_turns"], lower, upper, matrix)
    combined, strips = minorant(
        kernel, matrix, certificate["reference_turns"], lower, upper, arcs, certificate["parts"])
    eta, n = list(map(F, certificate["signed_eta"])), kernel["B"]-1
    if len(eta) != n or any(abs(value) > 10**60 for value in eta):
        raise ValueError("NEW integrated certificate has invalid signed curvature diagonal")
    error = F(n, hull.quadratic.ROUND_GRID)
    tested = [[value+(eta[i]-error if i == j else 0)
               for j, value in enumerate(row)] for i, row in enumerate(combined)]
    pivots = hull.quadratic.positive_ldl(tested)
    point, gradient = hull.outward_point_values(kernel, ref, arcs)
    support_value, support_check = hull.support(
        ref, lo, hi, matrix, gradient, eta, certificate["difference_dual"])
    lower_energy = point+support_value
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2*weight_sum
    normalized, grid = max(F(0), lower_energy)/weight_sum, 10**100
    radius_lower = F(isqrt(normalized.numerator*grid**2//normalized.denominator), grid)
    if not radius_lower**2 <= normalized < (radius_lower+F(1, grid))**2:
        raise AssertionError("NEW integrated positive-support radius conversion is not outward")
    return {
        "boundary_NEW_support_energy_lower": str(lower_energy),
        "NEW_support_whole_original_rod_energy_upper": str(upper_energy),
        "strict_energy_margin": str(lower_energy-upper_energy),
        "strict_radius_margin": str(radius_lower-F(radius)),
        "arithmetic_strict_target_test_passed": lower_energy > upper_energy and radius_lower > F(radius),
        "NEW_positive_weights_NOT_original_fixed_kernel_weights": True,
        "original_fixed_kernel_identity_flag_NOT_forged": True,
        "same_original_92_rods_fresh_exact_inverse_harmonic_Schur_and_NEW_weight_sum_checked": True,
        "exact_positive_LDL_and_full_rational_reconstruction_checked": True,
        "exact_LDL_minimum_pivot": str(min(pivots)),
        "weighted_symmetric_rounding_operator_error_charged": str(error),
        **strips, **support_check,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_original_model_source_history_geometry_gate_NOT_performed": True,
    }
