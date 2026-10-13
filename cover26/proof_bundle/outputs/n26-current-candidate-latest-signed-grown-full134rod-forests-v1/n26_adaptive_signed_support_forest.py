"""Distinct extension of preserved forests by NEW-support signed energy leaves."""

from copy import deepcopy
from fractions import Fraction as F

import n26_adaptive_rod_support_forest as prior
import n26_alternative_signed_hull_energy as signed


KIND = "ALTERNATIVE-SIGNED-ENERGY"
KINDS = (*prior.KINDS, KIND)


def partition(matrix, row, nodes, contractor, breadth_first):
    view = []
    for node in nodes:
        if not isinstance(node, dict) or node.get("kind") not in KINDS:
            raise ValueError("adaptive signed support forest has an unknown proof mode")
        view.append({"kind": "OPEN"} if node["kind"] == KIND else node)
    leaves = prior.partition(matrix, row, view, contractor, breadth_first)
    for leaf in leaves:
        if nodes[leaf["index"]]["kind"] == KIND:
            leaf["kind"] = KIND
    return leaves


def replay(original, kernel, arcs, row, nodes, supports):
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("adaptive signed support forest has no entire-root partition")
    dfs = partition(original["matrix"], row, nodes, prior.tighten, False)
    bfs = partition(original["matrix"], row, nodes, prior.independently_contract, True)
    if dfs != bfs:
        raise ValueError("adaptive signed support independent closed domains disagree")
    view = [{"kind": "OPEN"} if node["kind"] == KIND else deepcopy(node) for node in nodes]
    old_result, old_pending, ledger = prior.replay(original, kernel, arcs, row, view, supports)
    new_indices = {leaf["index"] for leaf in dfs if leaf["kind"] == KIND}
    pending = [leaf for leaf in old_pending if leaf["index"] not in new_indices]
    margins, used = [], set(old_result["alternative_supports_used_by_strict_closed_leaves"])
    for leaf in dfs:
        if leaf["kind"] != KIND:
            continue
        node = nodes[leaf["index"]]
        if set(node) != {"kind", "support_index", "certificate"}:
            raise ValueError("adaptive NEW signed leaf has unknown or missing proof fields")
        index = node["support_index"]
        if type(index) is not int or not 0 <= index < len(supports):
            raise ValueError("adaptive NEW signed leaf names an invalid positive support")
        result = signed.bound(
            original["reference"], supports[index], original["matrix"],
            leaf["lower"], leaf["upper"], node["certificate"], original["radius"], arcs)
        if (not result["arithmetic_strict_target_test_passed"]
                or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0):
            raise ValueError("adaptive NEW signed leaf lacks an exact strict whole-closed-box margin")
        margins.append(F(result["strict_radius_margin"]))
        used.add(index)
        ledger.append({**leaf, "support_index": index, "certificate": node["certificate"],
                       "arithmetic_result": result})
    counts = {kind: sum(node["kind"] == kind for node in nodes) for kind in KINDS}
    result = {
        **old_result, "counts": counts, "alternative_supports_used_by_strict_closed_leaves": sorted(used),
        "NEW_signed_support_leaves_exactly_reconstructed": len(new_indices),
        "minimum_NEW_signed_support_strict_radius_margin": str(min(margins)) if margins else None,
        "arithmetic_entire_root_lower_bound_cover_completed": not pending,
        "arithmetic_entire_root_strictly_empty": not pending and counts["LOCAL"] == 0,
        "retained_OPEN_leaves": len(pending),
        "NEW_signed_support_mode_not_relabelled_as_old_fixed_curvature": True,
    }
    return result, pending, sorted(ledger, key=lambda leaf: leaf["index"])
