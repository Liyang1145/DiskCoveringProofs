"""Unadmitted exact closed product-energy/LOCAL forest arithmetic."""

from collections import deque
from fractions import Fraction as F

import n26_candidate_energy_local_forest as original_forest
import n26_difference_product_curvature as product
from n26_sharp_radius_constraints import tighten
from verify_selected_type_trees import independently_contract


KINDS = ("SPLIT", "PRODUCT-ENERGY", "LOCAL", "EMPTY", "OPEN")


def partition(matrix, row, nodes, contractor, breadth_first):
    queue = deque([(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])))])
    seen, leaves = set(), []
    while queue:
        index, lower, upper = queue.popleft() if breadth_first else queue.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("product candidate forest hides or repeats a node")
        seen.add(index)
        node = nodes[index]
        if not isinstance(node, dict) or node.get("kind") not in KINDS:
            raise ValueError("product candidate forest has an unknown node kind")
        box = contractor(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("exact empty product forest domain not labelled EMPTY")
            leaves.append({"index": index, "kind": "EMPTY"})
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            children = original_forest.split(node, index, lower, upper, len(nodes))
            queue.extend(children if breadth_first else reversed(children))
        elif node["kind"] in ("PRODUCT-ENERGY", "LOCAL", "OPEN"):
            leaves.append({
                "index": index, "kind": node["kind"],
                "lower": list(map(str, lower)), "upper": list(map(str, upper))})
        else:
            raise ValueError("nonempty product forest region falsely called EMPTY")
    if len(seen) != len(nodes):
        raise ValueError("product forest has an unreachable hidden node")
    return sorted(leaves, key=lambda row: row["index"])


def replay(original, kernel, arcs, row, nodes):
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("product forest has no complete root partition")
    dfs = partition(original["matrix"], row, nodes, tighten, False)
    bfs = partition(original["matrix"], row, nodes, independently_contract, True)
    if dfs != bfs:
        raise ValueError("product forest independent BFS/DFS closed leaf domains disagree")
    counts = {kind: sum(node["kind"] == kind for node in nodes) for kind in KINDS}
    if counts["SPLIT"] + 1 != len(dfs):
        raise ValueError("product forest lost a complete closed sibling")
    pending, ledger, energy_margins, local_margins = [], [], [], []
    for leaf in dfs:
        node = nodes[leaf["index"]]
        if node["kind"] == "OPEN":
            if node != {"kind": "OPEN"}:
                raise ValueError("unproved product OPEN has supplied proof fields")
            pending.append(leaf)
        elif node["kind"] == "PRODUCT-ENERGY":
            if set(node) != {"kind", "certificate"}:
                raise ValueError("product energy leaf has unknown proof fields")
            result = product.bound(
                kernel, original["matrix"], leaf["lower"], leaf["upper"],
                node["certificate"], original["radius"], arcs)
            if (not result["arithmetic_strict_target_test_passed"]
                    or F(result["strict_energy_margin"]) <= 0
                    or F(result["strict_radius_margin"]) <= 0):
                raise ValueError("product candidate leaf lacks a strict exact margin")
            energy_margins.append(F(result["strict_radius_margin"]))
            ledger.append({**leaf, "certificate": node["certificate"], "arithmetic_result": result})
        elif node["kind"] == "LOCAL":
            if node != {"kind": "LOCAL"}:
                raise ValueError("product forest LOCAL must be freshly reconstructed")
            result = original_forest.local_proof(
                original, list(map(F, leaf["lower"])), list(map(F, leaf["upper"])))
            local_margins.append(F(result["strict_original_LOCAL_entry_margin"]))
            ledger.append({**leaf, "original_LOCAL_result": result})
        else:
            ledger.append(leaf)
    return {
        "nodes": len(nodes), "counts": counts,
        "entire_actual_source_closed_root_partition_checked": True,
        "two_independent_exact_closed_leaf_contractions_agreed": True,
        "arithmetic_entire_root_lower_bound_cover_completed": not pending,
        "arithmetic_entire_root_strictly_empty": not pending and counts["LOCAL"] == 0,
        "retained_OPEN_leaves": len(pending),
        "minimum_strict_product_energy_radius_margin": str(min(energy_margins)) if energy_margins else None,
        "minimum_original_LOCAL_entry_margin": str(min(local_margins)) if local_margins else None,
        "original_52_coordinate_LOCAL_allowance_unchanged": "7/800000",
        "LOCAL_equality_regions_not_declared_empty": True,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_source_model_ownership_admission_still_required": True,
    }, pending, ledger
