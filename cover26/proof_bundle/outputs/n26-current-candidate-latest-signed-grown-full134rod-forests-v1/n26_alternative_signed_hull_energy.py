"""NEW signed Taylor support with explicitly NEW positive original-rod weights.

No old fixed-kernel flag is forged. The exact original edge match and fresh
positive grounded inverse are checked before using generic Taylor arithmetic.
"""

from fractions import Fraction as F
from math import isqrt

import n26_reweighted_candidate_energy as alternative
import n26_signed_hull_energy_minorant as hull


def bound(original_reference, support, matrix, lower, upper, certificate, radius, arcs):
    kernel = alternative.kernel_gate(original_reference, support["reference"], support["inverse"])
    if set(certificate) != {"reference_turns", "signed_eta", "difference_dual"}:
        raise ValueError("alternative signed-hull certificate has unknown or missing fields")
    ref, lo, hi, hull_lo, hull_hi = hull.hull_gate(
        certificate["reference_turns"], lower, upper, matrix)
    diagonal = list(map(F, certificate["signed_eta"]))
    curvature = hull.signed_curvature_gate(kernel, matrix, hull_lo, hull_hi, diagonal, arcs)
    point, gradient = hull.outward_point_values(kernel, ref, arcs)
    support_lower, support_check = hull.support(
        ref, lo, hi, matrix, gradient, diagonal, certificate["difference_dual"])
    lower_energy = point+support_lower
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2 * weight_sum
    normalized = max(F(0), lower_energy)/weight_sum
    grid = 10**100
    numerator = isqrt(normalized.numerator * grid**2 // normalized.denominator)
    radius_lower = F(numerator, grid)
    if not radius_lower**2 <= normalized < (radius_lower+F(1, grid))**2:
        raise AssertionError("alternative signed-hull radius conversion was not outward")
    return {
        "boundary_NEW_support_energy_lower": str(lower_energy),
        "NEW_support_whole_original_rod_energy_upper": str(upper_energy),
        "strict_energy_margin": str(lower_energy-upper_energy),
        "strict_radius_margin": str(radius_lower-F(radius)),
        "arithmetic_strict_target_test_passed":
            lower_energy > upper_energy and radius_lower > F(radius),
        "NEW_positive_weights_NOT_original_fixed_kernel_weights": True,
        "same_original_92_rod_edges_fresh_ground_inverse_and_NEW_weight_sum_checked": True,
        "original_fixed_kernel_identity_flag_NOT_forged": True,
        **curvature, **support_check,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_source_model_history_geometry_admission_still_required": True,
    }
