"""Exact sequential closed-slab cover arithmetic, not source admission.

Given a separately reconstructed original model and actual current root row,
this checks every slab and the entire remaining original LOCAL box afresh.
No accepted per-root forest is changed by this module.
"""

from fractions import Fraction as F

import n26_candidate_energy_local_forest as forest
import n26_signed_hull_energy_minorant as hull
from n26_sharp_radius_constraints import tighten
from verify_selected_type_trees import independently_contract


def partition(matrix, row, cover, contractor):
    if (cover["source_OPEN_index"] != row["index"]
            or cover["actual_source_closed_box"] != row
            or not isinstance(cover["sequential_closed_slabs"], list)
            or not cover["sequential_closed_slabs"]):
        raise ValueError("signed-hull cover changed its entire actual source root")
    box = contractor(matrix, row["sharp_lower"], row["sharp_upper"])
    if box is None:
        raise ValueError("signed-hull cover does not expect an already empty source")
    lower, upper = box
    partitions = []
    for slab in cover["sequential_closed_slabs"]:
        axis, cut, side = slab["axis"], F(slab["cut"]), slab["side"]
        if (type(axis) is not int or not 0 <= axis < 15
                or not lower[axis] < cut < upper[axis]
                or side not in ("left", "right")
                or slab["both_closed_halves_include_shared_cut"] is not True
                or slab["parent_closed_lower"] != list(map(str, lower))
                or slab["parent_closed_upper"] != list(map(str, upper))):
            raise ValueError("signed-hull cover lost a closed half or actual parent domain")
        slab_lower, slab_upper = list(lower), list(upper)
        if side == "left":
            slab_upper[axis] = cut
        else:
            slab_lower[axis] = cut
        part = contractor(matrix, slab_lower, slab_upper)
        partitions.append(part)
        if side == "left":
            lower[axis] = cut
        else:
            upper[axis] = cut
        box = contractor(matrix, lower, upper)
        if box is None:
            raise ValueError("signed-hull cover omitted its final nonempty LOCAL remainder")
        lower, upper = box
    central = cover["central_closed_box"]
    if (central["closed_lower"] != list(map(str, lower))
            or central["closed_upper"] != list(map(str, upper))):
        raise ValueError("signed-hull cover clipped or changed its central remainder")
    return partitions, (lower, upper)


def replay(original, kernel, arcs, row, cover):
    parts, central = partition(original["matrix"], row, cover, tighten)
    independent, independent_central = partition(
        original["matrix"], row, cover, independently_contract)
    if parts != independent or central != independent_central:
        raise ValueError("signed-hull independent closed-slab contraction disagrees")
    margins, ledger, strict, empty = [], [], 0, 0
    for number, (slab, box) in enumerate(zip(cover["sequential_closed_slabs"], parts)):
        if box is None:
            if slab["kind"] != "EMPTY":
                raise ValueError("empty signed-hull slab has a geometric payment label")
            empty += 1
            ledger.append({"slab_index": number, "kind": "EMPTY"})
            continue
        lower, upper = box
        if (slab["kind"] != "SIGNED-HULL-ENERGY"
                or slab["sharp_lower"] != list(map(str, lower))
                or slab["sharp_upper"] != list(map(str, upper))):
            raise ValueError("signed-hull slab changed its entire closed sharp domain")
        result = hull.bound(
            kernel, original["matrix"], lower, upper, slab["certificate"],
            original["radius"], arcs)
        if (not result["arithmetic_strict_exclusion_test_passed"]
                or F(result["minimum_strict_energy_margin"]) <= 0
                or F(result["minimum_strict_radius_margin"]) <= 0):
            raise ValueError("signed-hull slab lacks a strict exact energy/radius margin")
        # Any supplied discovery result is informational; it cannot substitute
        # for the fresh exact computation above.
        if slab.get("arithmetic_result") != result:
            raise ValueError("signed-hull discovery arithmetic result did not reconstruct")
        margins.append(F(result["minimum_strict_radius_margin"]))
        strict += 1
        ledger.append({"slab_index": number, "kind": "SIGNED-HULL-ENERGY", **result})
    local = forest.local_proof(original, *central)
    if cover["central_closed_box"].get("original_LOCAL_result") != local:
        raise ValueError("signed-hull central original LOCAL result did not reconstruct")
    return {
        "source_OPEN_index": row["index"],
        "entire_actual_source_closed_root_covered_by_closed_slabs_and_LOCAL": True,
        "two_independent_exact_contractions_and_all_shared_boundaries_checked": True,
        "strict_signed_hull_energy_slabs": strict,
        "combinatorially_empty_slabs": empty,
        "minimum_strict_signed_hull_radius_margin": str(min(margins)) if margins else None,
        "original_LOCAL_entry_margin": local["strict_original_LOCAL_entry_margin"],
        "original_52_coordinate_LOCAL_allowance_unchanged": "7/800000",
        "LOCAL_equality_region_not_declared_empty": True,
        "accepted_owned_forest_history_not_changed_by_this_arithmetic_lemma": True,
        "source_model_latest_ownership_acceptance_still_required": True,
        "new_geometric_payments_by_this_arithmetic_module": 0,
        "ledger": ledger,
    }
