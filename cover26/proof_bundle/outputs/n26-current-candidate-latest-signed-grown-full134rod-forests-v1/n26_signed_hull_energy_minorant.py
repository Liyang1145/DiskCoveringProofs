"""Unadmitted exact signed-curvature Taylor minorant on a reference hull.

This is a new arithmetic lemma, NOT an accepted candidate/source interface.
Its callers still need the original-model gate, complete latest ownership
replay, frozen independent acceptance and actual publication replay.
"""

from fractions import Fraction as F
from math import isqrt

import n26_quadratic_energy_minorant as quadratic
from n26_sharp_radius_constraints import SCALE


VALUE_GRID = 10**80


def outward_point_values(kernel, reference, arcs):
    energy, gradient = quadratic.point_energy_gradient(kernel, reference, arcs)
    rounded_energy = F(energy.numerator * VALUE_GRID // energy.denominator, VALUE_GRID)
    rounded_gradient = [
        (F(a.numerator * VALUE_GRID // a.denominator, VALUE_GRID),
         F(-((-c.numerator * VALUE_GRID) // c.denominator), VALUE_GRID))
        for a, c in gradient
    ]
    if (not 0 <= energy - rounded_energy < F(1, VALUE_GRID)
            or any(not (al <= a <= c <= cu
                        and a - al < F(1, VALUE_GRID)
                        and cu - c < F(1, VALUE_GRID))
                   for (a, c), (al, cu) in zip(gradient, rounded_gradient))):
        raise AssertionError("signed-hull point/gradient rounding was not outward")
    return rounded_energy, rounded_gradient


def coordinate_minimum(a, c, g_lower, g_upper, eta):
    """Minimum of min(g_lower*d,g_upper*d)-eta*d*d/2 on [a,c]."""
    a, c, g_lower, g_upper, eta = map(F, (a, c, g_lower, g_upper, eta))
    if a > c or g_lower > g_upper:
        raise ValueError("invalid signed-curvature coordinate domain")
    points = {a, c}
    if a <= 0 <= c:
        points.add(F(0))
    if eta < 0:
        # Positive-curvature stationary points, separately for each sign.
        for gradient, left, right in (
            (g_upper, a, min(c, F(0))),
            (g_lower, max(a, F(0)), c),
        ):
            point = gradient / eta
            if left <= point <= right:
                points.add(point)
    return min(min(g_lower * d, g_upper * d) - eta * d * d / 2
               for d in points)


def hull_gate(reference_turns, lower, upper, matrix):
    ref = list(map(F, reference_turns))
    lo, hi = list(map(F, lower)), list(map(F, upper))
    b = len(matrix)
    if (len(ref) != b - 1 or len(lo) != b - 1 or len(hi) != b - 1
            or any(len(row) != b for row in matrix)
            or any(a > c for a, c in zip(lo, hi))):
        raise ValueError("invalid signed-hull reference/domain dimensions")
    hull_lo = [min(a, r) for a, r in zip(lo, ref)]
    hull_hi = [max(c, r) for c, r in zip(hi, ref)]
    # This checks all reference difference constraints even when the reference
    # is outside the target box. The necessary domain is convex.
    quadratic.reference_gate(ref, hull_lo, hull_hi, matrix)
    return [F(0), *ref], [F(0), *lo], [F(0), *hi], hull_lo, hull_hi


def signed_curvature_gate(kernel, matrix, hull_lo, hull_hi, diagonal, arcs):
    eta = list(map(F, diagonal))
    n = kernel["B"] - 1
    if len(eta) != n or any(abs(value) > 10**60 for value in eta):
        raise ValueError("invalid signed-curvature diagonal")
    hessian = quadratic.hessian_minorant(kernel, matrix, hull_lo, hull_hi, arcs)
    test = [[value + (eta[i] - F(n, quadratic.ROUND_GRID) if i == j else 0)
             for j, value in enumerate(row)] for i, row in enumerate(hessian)]
    pivots = quadratic.positive_ldl(test)
    return {
        "signed_curvature_diagonal": list(map(str, eta)),
        "exact_positive_LDL_and_full_reconstruction_checked": True,
        "symmetric_Hessian_rounding_spectral_error_charged": str(
            F(n, quadratic.ROUND_GRID)),
        "positive_curvature_coordinates": sum(value < 0 for value in eta),
        "all_Taylor_segments_in_reference_hull_and_necessary_difference_domain": True,
        "exact_LDL_minimum_pivot": str(min(pivots)),
    }


def support(reference, lower, upper, matrix, gradient, diagonal, dual):
    b, q = len(reference), dual["q"]
    if (type(q) is not int or not 0 < q <= 10**60
            or not isinstance(dual["terms"], list)):
        raise ValueError("invalid signed-hull difference dual")
    seen, divergence, constant = set(), [F(0)] * b, F(0)
    for term in dual["terms"]:
        if (not isinstance(term, list) or len(term) != 3
                or any(type(i) is not int or not 0 <= i < b for i in term[:2])
                or term[0] == term[1]):
            raise ValueError("invalid signed-hull difference-dual indices")
        i, j, raw = term
        numerator = int(raw)
        if numerator < 0 or numerator.bit_length() > 800 or (i, j) in seen:
            raise ValueError("negative or duplicate signed-hull multiplier")
        seen.add((i, j))
        mu = F(numerator, q)
        divergence[i] -= mu
        divergence[j] += mu
        constant += mu * (
            reference[j] - reference[i] - F(matrix[i][j], SCALE))
    contributions = [
        coordinate_minimum(
            lower[k] - reference[k], upper[k] - reference[k],
            gradient[k][0] + divergence[k], gradient[k][1] + divergence[k],
            diagonal[k - 1])
        for k in range(1, b)
    ]
    return constant + sum(contributions), {
        "nonnegative_difference_dual_terms": len(seen),
        "exact_gradient_intervals_and_piecewise_coordinate_minima_charged": True,
        "coordinate_contributions": list(map(str, contributions)),
    }


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    if (kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not True
            or kernel["B"] != 16 or kernel["vertices"] != 62
            or len(kernel["weights"]) != 92):
        raise ValueError("signed hull requires the unchanged original 92-rod kernel")
    if set(certificate) != {"reference_turns", "signed_eta", "difference_dual"}:
        raise ValueError("unknown or missing signed-hull certificate fields")
    ref, lo, hi, hull_lo, hull_hi = hull_gate(
        certificate["reference_turns"], lower, upper, matrix)
    eta = list(map(F, certificate["signed_eta"]))
    curvature = signed_curvature_gate(kernel, matrix, hull_lo, hull_hi, eta, arcs)
    reference_energy, gradient = outward_point_values(kernel, ref, arcs)
    signed_support, dual_check = support(
        ref, lo, hi, matrix, gradient, eta, certificate["difference_dual"])
    lower_energy = reference_energy + signed_support
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2 * weight_sum
    normalized = max(F(0), lower_energy) / weight_sum
    root_scale = 10**100
    root_num = isqrt(normalized.numerator * root_scale**2 // normalized.denominator)
    radius_lower = F(root_num, root_scale)
    if not radius_lower**2 <= normalized < (radius_lower + F(1, root_scale))**2:
        raise AssertionError("signed-hull exact outward radius conversion failed")
    margin = lower_energy - upper_energy
    if margin > 0 and radius_lower <= F(radius):
        raise ValueError("strict signed-hull diagnostic needs a finer radius endpoint")
    return {
        "boundary_quadratic_energy_lower": str(lower_energy),
        "same_root_whole_rod_energy_upper": str(upper_energy),
        "minimum_strict_energy_margin": str(margin),
        "minimum_strict_radius_margin": str(radius_lower - F(radius)),
        "required_radius_lower": str(radius_lower),
        "arithmetic_strict_exclusion_test_passed": margin > 0,
        "reference_energy_lower": str(reference_energy),
        "exact_signed_quadratic_support_lower": str(signed_support),
        "reference_outside_target_closed_box": any(
            not a <= r <= c for r, a, c in zip(ref, lo, hi)),
        "reference_feasible_in_necessary_difference_domain": True,
        "exact_reference_energy_and_gradient_outward_rounding_grid": VALUE_GRID,
        "all_point_value_rounding_errors_charged_outward": True,
        "reference_hull_lower": list(map(str, hull_lo)),
        "reference_hull_upper": list(map(str, hull_hi)),
        "original_92_positive_rods_52_coordinate_LOCAL_model_not_replaced": True,
        **curvature, **dual_check,
    }
