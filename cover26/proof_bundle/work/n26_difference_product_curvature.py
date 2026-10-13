"""Unadmitted Taylor minorant using products of necessary difference slacks.

This is arithmetic only. It does not replace the full source/model/history
gate, accept any leaf/root, or modify the existing frozen curvature modes.
"""

from fractions import Fraction as F
from math import isqrt

import n26_integrated_hull_curvature as integrated
from n26_sharp_radius_constraints import SCALE


def difference_slack(matrix, reference, pair):
    b = len(matrix)
    if (not isinstance(pair, list) or len(pair) != 2
            or any(type(index) is not int or not 0 <= index < b for index in pair)
            or pair[0] == pair[1]):
        raise ValueError("invalid necessary difference-slack indices")
    i, j = pair
    slack = F(matrix[i][j], SCALE) - reference[j] + reference[i]
    if slack < 0:
        raise ValueError("difference-product reference violates a necessary constraint")
    vector = [F(0)] * (b - 1)
    if i:
        vector[i - 1] += 1
    if j:
        vector[j - 1] -= 1
    return slack, vector


def product_data(matrix, reference, products):
    if not isinstance(products, list) or not 1 <= len(products) <= 64:
        raise ValueError("difference-product certificate needs explicit bounded products")
    result, seen = [], set()
    for item in products:
        if (not isinstance(item, dict)
                or set(item) != {"first_constraint", "second_constraint", "multiplier"}):
            raise ValueError("unknown or missing difference-product certificate fields")
        multiplier = F(item["multiplier"])
        if not 0 <= multiplier <= 10**60:
            raise ValueError("negative or excessive nonnegative-slack-product multiplier")
        u, a = difference_slack(matrix, reference, item["first_constraint"])
        v, b = difference_slack(matrix, reference, item["second_constraint"])
        key = tuple(sorted((tuple(item["first_constraint"]), tuple(item["second_constraint"]))))
        if key in seen:
            raise ValueError("duplicate necessary slack product")
        seen.add(key)
        result.append((multiplier, u, a, v, b))
    return result


def corrected_matrix(minorant, products):
    n = len(minorant)
    return [
        [value - sum(multiplier * (a[i] * b[j] + b[i] * a[j])
                     for multiplier, _, a, _, b in products)
         for j, value in enumerate(row)]
        for i, row in enumerate(minorant)
    ]


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    if set(certificate) != {"reference_turns", "parts", "signed_eta", "products"}:
        raise ValueError("unknown or missing difference-product Taylor certificate")
    ref, lo, hi, _, _ = integrated.hull.hull_gate(
        certificate["reference_turns"], lower, upper, matrix)
    minorant, strips = integrated.integrated_minorant(
        kernel, matrix, certificate["reference_turns"], lower, upper,
        arcs, certificate["parts"])
    products = product_data(matrix, ref, certificate["products"])
    corrected = corrected_matrix(minorant, products)
    eta = list(map(F, certificate["signed_eta"]))
    n = kernel["B"] - 1
    if len(eta) != n or any(abs(value) > 10**60 for value in eta):
        raise ValueError("invalid difference-product signed curvature diagonal")
    tested = [
        [value + (eta[i] - F(n, integrated.hull.quadratic.ROUND_GRID)
                  if i == j else 0)
         for j, value in enumerate(row)]
        for i, row in enumerate(corrected)
    ]
    pivots = integrated.hull.quadratic.positive_ldl(tested)
    point, gradient = integrated.hull.outward_point_values(kernel, ref, arcs)
    constant = sum(multiplier * u * v for multiplier, u, _, v, _ in products)
    shifted = [gradient[0]]
    for i in range(n):
        adjustment = sum(multiplier * (v * a[i] + u * b[i])
                         for multiplier, u, a, v, b in products)
        shifted.append(tuple(value - adjustment for value in gradient[i + 1]))
    support, support_check = integrated.hull.support(
        ref, lo, hi, matrix, shifted, eta, {"q": 1, "terms": []})
    lower_energy = point - constant + support
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2 * weight_sum
    normalized = max(F(0), lower_energy) / weight_sum
    grid = 10**100
    root_num = isqrt(normalized.numerator * grid**2 // normalized.denominator)
    radius_lower = F(root_num, grid)
    if not radius_lower**2 <= normalized < (radius_lower + F(1, grid))**2:
        raise AssertionError("difference-product radius conversion not outward")
    margin = lower_energy - upper_energy
    return {
        "boundary_energy_lower": str(lower_energy),
        "whole_original_rod_energy_upper": str(upper_energy),
        "strict_energy_margin": str(margin),
        "strict_radius_margin": str(radius_lower - F(radius)),
        "arithmetic_strict_target_test_passed": margin > 0 and radius_lower > F(radius),
        "nonnegative_necessary_difference_slack_products_checked": len(products),
        "reference_product_constant_charged": str(constant),
        "all_product_reference_linear_terms_charged": True,
        "exact_product_corrected_positive_LDL_and_reconstruction_passed": True,
        "exact_LDL_minimum_pivot": str(min(pivots)),
        "weighted_Hessian_rounding_operator_error_charged": str(
            F(n, integrated.hull.quadratic.ROUND_GRID)),
        "exact_normalized_Taylor_weights_sum": strips["exact_normalized_integral_weights_sum"],
        **support_check,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_original_model_source_history_gate_still_required": True,
    }
