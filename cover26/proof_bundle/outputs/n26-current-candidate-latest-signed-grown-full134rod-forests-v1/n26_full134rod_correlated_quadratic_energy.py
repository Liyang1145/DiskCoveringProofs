"""Distinct exact correlated quadratic support for a NEW134rod kernel.

Pure arithmetic, not source/history/geometry admission. No diagnostic or
typed-resource cache is imported. The old diagonal-support backend is intact.
"""

from fractions import Fraction as F
from math import isqrt

import n26_full_candidate_face_energy as full


SCHEMA = "N26-distinct-full134rod-correlated-quadratic-support-certificate-v1"


def quadratic_data(kernel, matrix, lower, upper, certificate, arcs):
    if (set(certificate) != {"schema", "reference_turns", "parts", "curvature_correction",
                            "quadratic_support_point", "difference_dual"}
            or certificate["schema"] != SCHEMA
            or kernel.get("distinct_full134rod_60free_positive_candidate_kernel") is not True
            or kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
            or kernel.get("alternative_positive_support_of_original_92_rods_NOT_original_fixed_weights") is not None
            or kernel["B"] != 16 or kernel["vertices"] != 76 or len(kernel["weights"]) != 134):
        raise ValueError("correlated quadratic support changed its explicit NEW134rod model/mode")
    ref, lo, hi, _, _ = full.hull.hull_gate(
        certificate["reference_turns"], lower, upper, matrix)
    correction = list(map(F, certificate["curvature_correction"]))
    point = list(map(F, certificate["quadratic_support_point"]))
    if (len(correction) != 15 or len(point) != 15
            or any(type(value) is bool for name in ("curvature_correction", "quadratic_support_point")
                   for value in certificate[name])
            or any(not 0 <= value <= 10**60 for value in correction)
            or any(abs(value) > 10**60 for value in point)):
        raise ValueError("correlated support has invalid nonnegative correction or support point")
    dual = certificate["difference_dual"]
    if (set(dual) != {"q", "terms"} or not isinstance(dual["terms"], list)
            or any(not isinstance(term, list) or len(term) != 3
                   or type(term[2]) not in (str, int) for term in dual["terms"])):
        raise ValueError("correlated support has unknown or noninteger dual proof fields")
    hessian = full.combined_minorant(
        kernel, matrix, certificate["reference_turns"], lower, upper, arcs, certificate["parts"])
    allowance = F(15, full.hull.quadratic.ROUND_GRID)
    quadratic = [[value+(correction[i]-allowance if i == j else 0)
                  for j, value in enumerate(row)] for i, row in enumerate(hessian)]
    pivots = full.hull.quadratic.positive_ldl(quadratic)
    lower_delta = [a-r for a, r in zip(lo[1:], ref[1:])]
    upper_delta = [b-r for b, r in zip(hi[1:], ref[1:])]
    energy, gradient = full.hull.outward_point_values(kernel, ref, arcs)
    # Choose the exact midpoint of every outward gradient interval and
    # explicitly charge its entire possible error over the actual closed box.
    midpoint_gradient = [(a+b)/2 for a, b in gradient[1:]]
    error = sum((b-a)/2*max(abs(x), abs(y)) for (a, b), x, y in zip(
        gradient[1:], lower_delta, upper_delta))
    linear = [g-eta*(a+b)/2 for g, eta, a, b in zip(
        midpoint_gradient, correction, lower_delta, upper_delta)]
    constant = sum(eta*a*b/2 for eta, a, b in zip(
        correction, lower_delta, upper_delta))-error
    return {
        "reference": ref, "lower": lo, "upper": hi,
        "lower_delta": lower_delta, "upper_delta": upper_delta,
        "quadratic": quadratic, "linear": linear,
        "constant": constant, "reference_energy_lower": energy,
        "support_point": point, "gradient_error": error,
        "rounding_operator_allowance": allowance,
        "minimum_LDL_pivot": min(pivots),
    }


def correlated_support(data, matrix, dual):
    point, quadratic = data["support_point"], data["quadratic"]
    q_point = [sum(row[j]*point[j] for j in range(15)) for row in quadratic]
    tangent = [value+linear for value, linear in zip(q_point, data["linear"])]
    # The existing exact linear difference-domain support is used only AFTER
    # explicit NEW134rod and exact positive-LDL gates above. It has no model
    # identity flag; eta=0 leaves only exact interval linear minima.
    linear_support, controls = full.hull.support(
        data["reference"], data["lower"], data["upper"], matrix,
        [(F(0), F(0)), *((value, value) for value in tangent)],
        [F(0)]*15, dual)
    quadratic_at_point = sum(value*other for value, other in zip(point, q_point))/2
    return linear_support-quadratic_at_point+data["constant"], {
        "exact_correlated_quadratic_at_support_point": str(quadratic_at_point),
        "exact_linear_difference_domain_support": str(linear_support),
        "concave_correction_closed_secants_and_gradient_error_constant": str(data["constant"]),
        **controls,
    }


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    data = quadratic_data(kernel, matrix, lower, upper, certificate, arcs)
    support, controls = correlated_support(data, matrix, certificate["difference_dual"])
    energy_lower = data["reference_energy_lower"]+support
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    energy_upper = F(radius)**2*weight_sum
    normalized, grid = max(F(0), energy_lower)/weight_sum, 10**100
    radius_lower = F(isqrt(normalized.numerator*grid**2//normalized.denominator), grid)
    if not radius_lower**2 <= normalized < (radius_lower+F(1, grid))**2:
        raise AssertionError("correlated quadratic support lost outward exact radius conversion")
    return {
        "boundary_full134rod_correlated_energy_lower": str(energy_lower),
        "NEW_full134rod_energy_upper_at_same_root": str(energy_upper),
        "strict_energy_margin": str(energy_lower-energy_upper),
        "strict_radius_margin": str(radius_lower-F(radius)),
        "arithmetic_strict_target_test_passed":
            energy_lower > energy_upper and radius_lower > F(radius),
        "distinct_full134rod_76vertex_60free_kernel_NOT_original92rod": True,
        "correlated_positive_quadratic_retained_NOT_diagonal_only_support": True,
        "support_point_is_an_arbitrary_rational_tangent_NOT_an_assumed_feasible_minimizer": True,
        "all_closed_Taylor_strips_and_exact_normalized_weights_sum1_checked": certificate["parts"],
        "weighted_symmetric_rounding_operator_error_charged": str(data["rounding_operator_allowance"]),
        "exact_positive_LDL_minimum_pivot": str(data["minimum_LDL_pivot"]),
        "outward_gradient_midpoint_error_explicitly_charged": str(data["gradient_error"]),
        **controls, "verified": False, "new_geometric_payments": 0,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
    }
