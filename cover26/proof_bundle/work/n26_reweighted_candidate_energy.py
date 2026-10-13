"""New positive support over exactly the original 92 necessary rod edges.

This is not the old fixed-weight kernel. The caller must still execute the
complete original geometry/source/history gate before any formal admission.
"""

from fractions import Fraction as F
from math import isqrt

import n26_dirichlet_energy as dirichlet


def kernel_gate(original_reference, alternative_reference, certificate):
    if (original_reference["N"] != 26 or original_reference["B"] != 16
            or len(original_reference["edges"]) != 92
            or alternative_reference["N"] != original_reference["N"]
            or alternative_reference["B"] != original_reference["B"]
            or alternative_reference["edges"] != original_reference["edges"]
            or alternative_reference["radius_scope"] != original_reference["radius_scope"]
            or alternative_reference["source_acceptance_sha256"]
            != original_reference["source_acceptance_sha256"]
            or alternative_reference["alternative_weights_are_DIAGNOSTIC_not_original_accepted_support"]
            is not True
            or alternative_reference["weight_numerators"] == original_reference["weight_numerators"]
            or int(alternative_reference["rational_scale"]) <= 0):
        raise ValueError("alternative support changed original rod geometry or relabelled the fixed kernel")
    kernel = dirichlet.kernel_gate(alternative_reference, certificate)
    return {
        **kernel, "B": 16, "vertices": 62, "edges": original_reference["edges"],
        "pairs": kernel["pair_weights"],
        "alternative_positive_support_of_original_92_rods_NOT_original_fixed_weights": True,
    }


def bound(original_reference, alternative_reference, inverse, lower, upper, radius, arcs):
    kernel = kernel_gate(original_reference, alternative_reference, inverse)
    result = dirichlet.bound(lower, upper, kernel, F(radius)**2, arcs)
    normalized = max(F(0), F(result["boundary_Dirichlet_energy_lower"])) / F(
        sum(kernel["weights"]), kernel["scale"])
    grid = 10**100
    integer = isqrt(normalized.numerator * grid**2 // normalized.denominator)
    radius_lower = F(integer, grid)
    if not radius_lower**2 <= normalized < (radius_lower+F(1, grid))**2:
        raise AssertionError("alternative support radius conversion not outward")
    return {
        **result, "strict_radius_margin": str(radius_lower-F(radius)),
        "same_original_92_positive_rod_edges_and_46_grounded_free_vertices_checked": True,
        "NEW_positive_support_NOT_the_original_fixed_weight_kernel": True,
        "verified": False, "new_geometric_payments": 0,
        "complete_original_geometry_source_and_latest_history_admission_still_required": True,
    }
