"""Arithmetic-only Taylor bounds using explicitly contained closed-box slacks.

For x in [a,b], (x-a)(b-x) >= 0. Subtracting its nonnegative
multiple from energy adds a positive diagonal to the Hessian. The value
AND linear term of the subtracted product at the reference are charged.
This does not modify or admit any historical curvature/source mode.
"""

from fractions import Fraction as F
from math import isqrt

import n26_difference_product_curvature as difference


def box_product_data(reference, lower, upper, items):
    n = len(reference)-1
    if not isinstance(items, list) or len(items) > n:
        raise ValueError("box-slack products need an explicitly bounded coordinate table")
    result, seen = [], set()
    for item in items:
        if (not isinstance(item, dict)
                or set(item) != {"axis", "closed_lower", "closed_upper", "multiplier"}
                or type(item["axis"]) is not int or not 0 <= item["axis"] < n):
            raise ValueError("unknown or malformed box-slack product fields")
        axis = item["axis"]
        if axis in seen:
            raise ValueError("duplicate coordinate box-slack product")
        seen.add(axis)
        a, b, multiplier = F(item["closed_lower"]), F(item["closed_upper"]), F(item["multiplier"])
        if (not a < b or not a <= lower[axis+1] <= upper[axis+1] <= b
                or not 0 <= multiplier <= 10**60):
            raise ValueError("box-slack product is negative or does not contain the actual closed domain")
        u, v = reference[axis+1]-a, b-reference[axis+1]
        left, right = [F(0)]*n, [F(0)]*n
        left[axis], right[axis] = F(1), F(-1)
        result.append((multiplier, u, left, v, right))
    return result


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    if set(certificate) != {
            "reference_turns", "parts", "signed_eta", "difference_products",
            "box_products", "difference_dual"}:
        raise ValueError("unknown or missing box-slack Taylor certificate fields")
    ref, lo, hi, _, _ = difference.integrated.hull.hull_gate(
        certificate["reference_turns"], lower, upper, matrix)
    raw = certificate["difference_products"]
    if not isinstance(raw, list):
        raise ValueError("box-slack certificate has an invalid difference-product table")
    products = difference.product_data(matrix, ref, raw) if raw else []
    boxes = box_product_data(ref, lo, hi, certificate["box_products"])
    if not products and not boxes:
        raise ValueError("box-slack certificate has no explicit nonnegative slack product")
    all_products = [*products, *boxes]
    minorant, strips = difference.integrated.integrated_minorant(
        kernel, matrix, certificate["reference_turns"], lower, upper, arcs, certificate["parts"])
    corrected = difference.corrected_matrix(minorant, all_products)
    eta, n = list(map(F, certificate["signed_eta"])), kernel["B"]-1
    if len(eta) != n or any(abs(value) > 10**60 for value in eta):
        raise ValueError("invalid box-slack signed curvature diagonal")
    error = F(n, difference.integrated.hull.quadratic.ROUND_GRID)
    tested = [[value+(eta[i]-error if i == j else 0)
               for j, value in enumerate(row)] for i, row in enumerate(corrected)]
    pivots = difference.integrated.hull.quadratic.positive_ldl(tested)
    point, gradient = difference.integrated.hull.outward_point_values(kernel, ref, arcs)
    constant = sum(multiplier*u*v for multiplier, u, _, v, _ in all_products)
    shifted = [gradient[0]]
    for i in range(n):
        adjustment = sum(multiplier*(v*a[i]+u*b[i])
                         for multiplier, u, a, v, b in all_products)
        shifted.append(tuple(value-adjustment for value in gradient[i+1]))
    support, support_check = difference.integrated.hull.support(
        ref, lo, hi, matrix, shifted, eta, certificate["difference_dual"])
    lower_energy = point-constant+support
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2*weight_sum
    normalized = max(F(0), lower_energy)/weight_sum
    grid = 10**100
    radius_lower = F(isqrt(normalized.numerator*grid**2//normalized.denominator), grid)
    if not radius_lower**2 <= normalized < (radius_lower+F(1, grid))**2:
        raise AssertionError("box-slack Taylor radius conversion is not outward")
    return {
        "boundary_energy_lower": str(lower_energy),
        "whole_original_rod_energy_upper": str(upper_energy),
        "strict_energy_margin": str(lower_energy-upper_energy),
        "strict_radius_margin": str(radius_lower-F(radius)),
        "arithmetic_strict_target_test_passed": lower_energy > upper_energy and radius_lower > F(radius),
        "actual_closed_box_contained_in_every_nonnegative_box_slack_domain": True,
        "nonnegative_box_slack_products_checked": len(boxes),
        "nonnegative_necessary_difference_slack_products_checked": len(products),
        "all_reference_product_constants_charged_including_outside_box_reference": str(constant),
        "all_reference_product_linear_terms_charged": True,
        "reference_outside_target_closed_box": any(not a <= r <= b for r, a, b in zip(ref, lo, hi)),
        "product_corrected_exact_positive_LDL_and_full_reconstruction_checked": True,
        "exact_LDL_minimum_pivot": str(min(pivots)),
        "weighted_Hessian_rounding_operator_error_charged": str(error),
        "exact_normalized_Taylor_weights_sum": strips["exact_normalized_integral_weights_sum"],
        **support_check,
        "original_fixed_92_rod_kernel_not_relabelled_or_reweighted": True,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_original_model_source_history_geometry_gate_NOT_performed": True,
    }
