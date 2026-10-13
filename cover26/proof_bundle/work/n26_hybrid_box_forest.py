"""Exact additive hybrid forests; the previously sealed energy-only gate is unchanged."""

from collections import deque
from fractions import Fraction as F

import n26_correlated_arc_force as correlated
import n26_quadratic_box_forest as original
import n26_quadratic_energy_minorant as energy
from n26_sharp_radius_constraints import tighten
from verify_selected_type_trees import independently_contract


KINDS = ("SPLIT", "QUADRATIC_ENERGY", "CORRELATED_FORCE", "EMPTY", "OPEN")


def independent_leaves(matrix, root_box, nodes):
    queue = deque([(0, list(map(F, root_box["lower"])), list(map(F, root_box["upper"])))])
    seen, leaves = set(), []
    while queue:
        index, lower, upper = queue.popleft()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("independent hybrid traversal repeats or hides a node")
        seen.add(index)
        node = nodes[index]
        if not isinstance(node, dict) or node.get("kind") not in KINDS:
            raise ValueError("invalid independent hybrid node")
        box = independently_contract(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("independent contradicted box was not EMPTY")
            leaves.append({"index": index, "kind": "EMPTY"})
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            queue.extend(original.split(node, lower, upper, len(nodes)))
        elif node["kind"] in ("OPEN", "QUADRATIC_ENERGY", "CORRELATED_FORCE"):
            leaves.append({"index": index, "kind": node["kind"],
                           "lower": list(map(str, lower)), "upper": list(map(str, upper))})
        else:
            raise ValueError("nonempty independent hybrid leaf falsely EMPTY")
    if len(seen) != len(nodes):
        raise ValueError("independent hybrid traversal has hidden nodes")
    return sorted(leaves, key=lambda row: row["index"])


def replay(spec, matrix, root_box, nodes, kernels, radius, arcs):
    if not isinstance(nodes, list) or not nodes or spec["N"] != 26 or spec["next"] != 26:
        raise ValueError("hybrid forest must have nodes and a complete 26-center graph")
    stack = [(0, list(map(F, root_box["lower"])), list(map(F, root_box["upper"])), 0)]
    seen, pending, ledger, leaves, margins = set(), [], [], [], []
    counts, maximum_depth = dict.fromkeys(KINDS, 0), 0
    while stack:
        index, lower, upper, depth = stack.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("hybrid forest repeats, cycles or loses a node")
        seen.add(index)
        maximum_depth = max(maximum_depth, depth)
        node = nodes[index]
        if not isinstance(node, dict) or node.get("kind") not in counts:
            raise ValueError("unknown hybrid node kind")
        kind = node["kind"]
        counts[kind] += 1
        box = tighten(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("contradicted hybrid box must be paid as EMPTY")
            row = {"index": index, "kind": "EMPTY"}
            leaves.append(row)
            ledger.append(row)
            continue
        lower, upper = box
        if kind == "SPLIT":
            stack.extend((*child, depth + 1)
                         for child in reversed(original.split(node, lower, upper, len(nodes))))
            continue
        row = {"index": index, "kind": kind,
               "lower": list(map(str, lower)), "upper": list(map(str, upper))}
        leaves.append(row)
        if kind == "OPEN":
            if node != {"kind": "OPEN"}:
                raise ValueError("hybrid OPEN has unverified fields")
            pending.append(row)
            continue
        if kind == "QUADRATIC_ENERGY":
            if set(node) != {"kind", "kernel_index", "certificate"}:
                raise ValueError("hybrid energy leaf has unverified fields")
            k = node["kernel_index"]
            if type(k) is not int or not 0 <= k < len(kernels) or kernels[k]["spec"] != spec:
                raise ValueError("hybrid energy kernel has different full graph")
            result = energy.bound(kernels[k], matrix, lower, upper, node["certificate"], radius, arcs)
            if (not result["radius_at_most_Rstar_whole_box_excluded"]
                    or F(result["minimum_strict_radius_margin"]) <= 0):
                raise ValueError("hybrid energy payment is not strict on the entire closed leaf")
            payment = {**row, "kernel_index": k, "certificate": node["certificate"], **result}
        elif kind == "CORRELATED_FORCE":
            if set(node) != {"kind", "certificate"}:
                raise ValueError("hybrid force leaf has unverified fields")
            result = correlated.force_check(spec, lower, upper, matrix, node["certificate"], arcs)
            margin = F(result["required_radius_lower"]) - radius
            if margin <= 0:
                raise ValueError("hybrid whole-box force payment is not strict")
            payment = {**row, "certificate": node["certificate"], **result,
                       "minimum_strict_radius_margin": str(margin)}
        else:
            raise ValueError("nonempty hybrid leaf falsely declared EMPTY")
        margins.append(F(payment["minimum_strict_radius_margin"]))
        ledger.append(payment)
    if len(seen) != len(nodes):
        raise ValueError("hybrid forest has hidden unvisited nodes")
    if sorted(leaves, key=lambda row: row["index"]) != independent_leaves(matrix, root_box, nodes):
        raise ValueError("independent hybrid BFS/DFS contracted leaf boxes differ")
    pending.sort(key=lambda row: row["index"])
    ledger.sort(key=lambda row: row["index"])
    return {
        "nodes": len(nodes), "counts": counts, "maximum_depth": maximum_depth,
        "source_entire_closed_OPEN_box_partitioned": True,
        "independent_BFS_DFS_leaf_boxes_matched": True,
        "source_OPEN_box_fully_excluded": not pending,
        "unresolved_closed_boxes": len(pending),
        "minimum_strict_radius_margin": str(min(margins)) if margins else None,
    }, pending, ledger
