"""Explicit expanded support table; preserve the old 32-support semantics."""

from copy import deepcopy
from fractions import Fraction as F

import n26_adaptive_signed_support_forest as prior


KIND, KINDS = prior.KIND, prior.KINDS
MAX_SUPPORTS = 256


def support_gate(original, supports):
    if not isinstance(supports, list) or not 32 <= len(supports) <= MAX_SUPPORTS:
        raise ValueError("extended signed support table must explicitly retain its original 32 entries")
    kernels = []
    for start in range(0, len(supports), 32):
        kernels.extend(prior.prior.support_gate(original, supports[start:start+32]))
    return kernels


def partition(matrix, row, nodes, contractor, breadth_first):
    return prior.partition(matrix, row, nodes, contractor, breadth_first)


def replay(original, kernel, arcs, row, nodes, supports):
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("extended signed forest has no complete source partition")
    dfs = partition(original["matrix"], row, nodes, prior.prior.tighten, False)
    bfs = partition(original["matrix"], row, nodes, prior.prior.independently_contract, True)
    if dfs != bfs:
        raise ValueError("extended signed support independent closed domains disagree")
    support_gate(original, supports)
    # Older direct alternative leaves belong to the original bounded table.
    # New entries may be used ONLY by the explicitly extended signed mode.
    for node in nodes:
        if (node["kind"] == "ALTERNATIVE-ENERGY"
                and (type(node.get("support_index")) is not int or not 0 <= node["support_index"] < 32)):
            raise ValueError("extended support cannot relabel a new entry as an old direct support")
    view = [{"kind": "OPEN"} if node["kind"] == KIND else deepcopy(node) for node in nodes]
    previous, provisional, ledger = prior.prior.replay(
        original, kernel, arcs, row, view, supports[:32])
    signed_indices = {leaf["index"] for leaf in dfs if leaf["kind"] == KIND}
    pending = [leaf for leaf in provisional if leaf["index"] not in signed_indices]
    margins, used = [], set(previous["alternative_supports_used_by_strict_closed_leaves"])
    for leaf in dfs:
        if leaf["kind"] != KIND:
            continue
        node = nodes[leaf["index"]]
        if set(node) != {"kind", "support_index", "certificate"}:
            raise ValueError("extended signed leaf has unknown or missing fields")
        index = node["support_index"]
        if type(index) is not int or not 0 <= index < len(supports):
            raise ValueError("extended signed leaf names an invalid positive support")
        result = prior.signed.bound(
            original["reference"], supports[index], original["matrix"],
            leaf["lower"], leaf["upper"], node["certificate"], original["radius"], arcs)
        if (not result["arithmetic_strict_target_test_passed"]
                or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0):
            raise ValueError("extended signed leaf has no exact strict energy/radius margin")
        margins.append(F(result["strict_radius_margin"]))
        used.add(index)
        ledger.append({**leaf, "support_index": index, "certificate": node["certificate"],
                       "arithmetic_result": result})
    counts = {kind: sum(node["kind"] == kind for node in nodes) for kind in KINDS}
    return {
        **previous, "counts": counts, "alternative_supports_checked": len(supports),
        "alternative_supports_used_by_strict_closed_leaves": sorted(used),
        "NEW_signed_support_leaves_exactly_reconstructed": len(signed_indices),
        "minimum_NEW_signed_support_strict_radius_margin": str(min(margins)) if margins else None,
        "arithmetic_entire_root_lower_bound_cover_completed": not pending,
        "arithmetic_entire_root_strictly_empty": not pending and counts["LOCAL"] == 0,
        "retained_OPEN_leaves": len(pending),
        "NEW_signed_support_mode_not_relabelled_as_old_fixed_curvature": True,
        "explicit_extended_positive_support_table_checked": True,
        "maximum_explicit_positive_support_table_entries": MAX_SUPPORTS,
    }, pending, sorted(ledger, key=lambda leaf: leaf["index"])
