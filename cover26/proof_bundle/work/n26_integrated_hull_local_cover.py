"""Exact integrated-Taylor root covers, without any current-source admission.

This pure arithmetic module does not import a typed diagnostic model. A
separate own-executor verifier must establish the actual original model,
source ownership and unchanged accepted per-root history.
"""

from copy import deepcopy
from fractions import Fraction as F
from math import isqrt

import n26_integrated_hull_curvature as integrated
import n26_signed_hull_local_cover as partition


def slab_bound(kernel, matrix, reference, root_box, slab_box, eta, radius, arcs):
    lower, upper = slab_box
    if (any(a < ra or c > rc for a, c, ra, rc in
            zip(lower, upper, root_box[0], root_box[1]))
            or any(a > c for a, c in zip(lower, upper))):
        raise ValueError("integrated slab is not contained in its certified root")
    ref, lo, hi, _, _ = integrated.hull.hull_gate(reference, lower, upper, matrix)
    point, gradient = integrated.hull.outward_point_values(kernel, ref, arcs)
    support, dual_check = integrated.hull.support(
        ref, lo, hi, matrix, gradient, eta, {"q": 1, "terms": []})
    lower_energy = point + support
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2 * weight_sum
    normalized = max(F(0), lower_energy) / weight_sum
    grid = 10**100
    root_num = isqrt(normalized.numerator * grid**2 // normalized.denominator)
    lower_radius = F(root_num, grid)
    if not lower_radius**2 <= normalized < (lower_radius + F(1, grid))**2:
        raise AssertionError("integrated radius conversion not outward")
    margin = lower_energy - upper_energy
    return {
        "boundary_energy_lower": str(lower_energy),
        "whole_original_rod_energy_upper": str(upper_energy),
        "strict_energy_margin": str(margin),
        "strict_radius_margin": str(lower_radius - F(radius)),
        "arithmetic_strict_slab_test_passed": margin > 0 and lower_radius > F(radius),
        "exact_zero_dual_support": str(support), **dual_check,
        "uses_freshly_checked_uniform_integral_root_certificate": True,
        "closed_slab_is_contained_in_certified_closed_root": True,
    }


def replay(original, kernel, arcs, actual_row, item):
    if (item["source_OPEN_index"] != actual_row["index"]
            or item["actual_source_closed_box"] != actual_row):
        raise ValueError("integrated cover changed actual whole-root ownership/domain")
    root_box = partition.tighten(
        original["matrix"], actual_row["sharp_lower"], actual_row["sharp_upper"])
    if root_box is None:
        raise ValueError("integrated cover supplied an already empty root")
    reference = list(map(F, item["reference_turns"]))
    raw = item["uniform_integral_root_curvature_certificate"]
    eta = list(map(F, raw["signed_eta"]))
    fresh = integrated.gate(
        kernel, original["matrix"], reference, *root_box, eta, arcs, raw["parts"])
    if fresh != raw:
        raise ValueError("integrated Taylor weights, strips or rounding certificate changed")
    parts, central = partition.partition(
        original["matrix"], actual_row, item, partition.tighten)
    other_parts, other_central = partition.partition(
        original["matrix"], actual_row, item, partition.independently_contract)
    if parts != other_parts or central != other_central:
        raise ValueError("integrated independent exact closed partitions disagree")
    margins, count = [], 0
    for slab, box in zip(item["sequential_closed_slabs"], parts):
        if box is None:
            if slab["kind"] != "EMPTY":
                raise ValueError("integrated empty slab labelled as nonempty energy")
            continue
        if (slab["kind"] != "INTEGRATED-HULL-ENERGY"
                or slab["sharp_lower"] != list(map(str, box[0]))
                or slab["sharp_upper"] != list(map(str, box[1]))):
            raise ValueError("integrated slab clipped its full closed domain")
        result = slab_bound(
            kernel, original["matrix"], reference, root_box, box, eta,
            original["radius"], arcs)
        if (result != slab["arithmetic_result"]
                or not result["arithmetic_strict_slab_test_passed"]
                or F(result["strict_energy_margin"]) <= 0
                or F(result["strict_radius_margin"]) <= 0):
            raise ValueError("integrated slab lacks fresh strict exact energy/radius margins")
        margins.append(F(result["strict_radius_margin"]))
        count += 1
    if not margins:
        raise ValueError("integrated cover supplied no nonempty strict energy slab")
    local = partition.forest.local_proof(original, *central)
    if local != item["central_closed_box"]["original_LOCAL_result"]:
        raise ValueError("integrated central original LOCAL certificate changed")
    return {
        "source_OPEN_index": actual_row["index"],
        "strict_integrated_slabs_checked": count,
        "minimum_strict_radius_margin": str(min(margins)),
        "original_LOCAL_entry_margin": local["strict_original_LOCAL_entry_margin"],
        "two_exact_closed_partitions_and_uniform_integral_root_gate_checked": True,
    }


def rejection_controls(original, kernel, arcs, actual_row, first):
    rejected = []

    def reject(name, mutation):
        bad = deepcopy(first)
        mutation(bad)
        try:
            replay(original, kernel, arcs, actual_row, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("invalid integrated cover accepted: " + name)

    reject("whole-root-ownership-changed",
           lambda bad: bad.update(source_OPEN_index=actual_row["index"] + 1))
    reject("first-closed-slab-omitted",
           lambda bad: bad["sequential_closed_slabs"].pop(0))
    reject("shared-slab-boundary-lost",
           lambda bad: bad["sequential_closed_slabs"][0].update(
               both_closed_halves_include_shared_cut=False))
    reject("central-remainder-clipped",
           lambda bad: bad["central_closed_box"]["closed_lower"].__setitem__(0, "0"))
    reject("Taylor-strip-omitted",
           lambda bad: bad["uniform_integral_root_curvature_certificate"]["closed_Taylor_strips"].pop(0))
    reject("Taylor-weight-unjustifiably-increased",
           lambda bad: bad["uniform_integral_root_curvature_certificate"]["closed_Taylor_strips"][0].update(
               normalized_Taylor_weight="1"))
    reject("weighted-rounding-operator-error-omitted",
           lambda bad: bad["uniform_integral_root_curvature_certificate"].update(
               weighted_symmetric_rounding_operator_error_charged="0"))
    reject("nonpositive-Taylor-partition-count",
           lambda bad: bad["uniform_integral_root_curvature_certificate"].update(parts=0))
    free = next(axis for axis, value in enumerate(
        first["uniform_integral_root_curvature_certificate"]["signed_eta"]) if F(value) < 0)
    reject("unsupported-integrated-positive-curvature",
           lambda bad: bad["uniform_integral_root_curvature_certificate"]["signed_eta"].__setitem__(
               free, "-1000000"))
    reject("infeasible-reference-outside-necessary-polytope",
           lambda bad: bad["reference_turns"].__setitem__(0, "100"))
    reject("strict-energy-margin-fabricated",
           lambda bad: bad["sequential_closed_slabs"][0]["arithmetic_result"].update(
               strict_energy_margin="1"))
    reject("original-LOCAL-allowance-expanded",
           lambda bad: bad["central_closed_box"]["original_LOCAL_result"].update(
               original_52_coordinate_local_allowance="1"))
    return rejected


def tiny_control(original, kernel, arcs, item):
    reference = list(map(F, item["reference_turns"]))
    certificate = item["uniform_integral_root_curvature_certificate"]
    eta = list(map(F, certificate["signed_eta"]))
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    box = partition.tighten(
        original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
    if box is None:
        raise ValueError("integrated control lost the known feasible tiny domain")
    # The feasible tiny box can be outside the target root. Recompute its OWN
    # integral domain; the target-root curvature must never be reused for it.
    integrated.gate(
        kernel, original["matrix"], reference, *box, eta, arcs, certificate["parts"])
    result = slab_bound(
        kernel, original["matrix"], reference, box, box, eta, original["radius"], arcs)
    if result["arithmetic_strict_slab_test_passed"]:
        raise AssertionError("integrated curvature falsely excludes the tiny feasible candidate")
    return {"source_OPEN_index": item["source_OPEN_index"],
            "known_feasible_tiny_candidate_not_strictly_excluded": True,
            "tiny_domain_integrated_curvature_freshly_checked": True}
