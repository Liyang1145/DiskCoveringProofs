"""Explicit adapter for the original 92-rod candidate Dirichlet kernel.

This accepts neither a generic full-type kernel nor a partial-prefix kernel.
Current candidate ownership, frame and local-barrier linkage are checked by
the semantically replayed Dirichlet source gate before this adapter is used.
"""

from fractions import Fraction as F

import n26_dirichlet_energy as dirichlet
import n26_quadratic_energy_minorant as quadratic


def kernel_gate(reference, certificate):
    edges = reference["edges"]
    scale = int(reference["rational_scale"])
    if (scale <= 0 or len(edges) != 92 or len(reference["weight_numerators"]) != 92
            or reference["radius_scope"] != "at-most-the-certified-same-root-Rstar"
            or certificate["schema"] != "N26-exact-integer-ground-Dirichlet-inverse-v1"
            or certificate["anchor_vertices"] != 16):
        raise ValueError("candidate curvature adapter requires the original grounded 92-rod support")
    kernel = dirichlet.kernel_gate(reference, certificate)
    if (len(kernel["matrix"]) != 62 or len(kernel["inverse"]) != 46
            or len(kernel["harmonic"]) != 46 or any(len(row) != 16 for row in kernel["harmonic"])):
        raise ValueError("candidate curvature adapter changed the original 62-vertex graph")
    return {**kernel, "B": 16, "vertices": 62, "edges": edges, "pairs": kernel["pair_weights"],
            "original_candidate_92_rod_46_free_vertex_kernel": True}


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    if (kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not True
            or kernel["B"] != 16 or kernel["vertices"] != 62 or len(kernel["weights"]) != 92):
        raise ValueError("a different graph was supplied to the original candidate energy adapter")
    result = quadratic.bound(kernel, matrix, lower, upper, certificate, radius, arcs)
    return {**result, "candidate_same_root_whole_closed_box_excluded": result[
        "radius_at_most_Rstar_whole_box_excluded"],
            "original_92_positive_rods_and_46_grounded_free_vertices_preserved": True,
            "no_full_type_or_partial_prefix_kernel_relabelled_as_candidate": True}


def strict_gate(result):
    if (not result["candidate_same_root_whole_closed_box_excluded"]
            or F(result["minimum_strict_energy_margin"]) <= 0
            or F(result["minimum_strict_radius_margin"]) <= 0):
        raise ValueError("candidate curvature energy exclusion is not strictly proved")
