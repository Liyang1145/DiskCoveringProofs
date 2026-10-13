"""Exact closed-half energy forests with independent BFS box reconstruction."""

from collections import deque
from fractions import Fraction as F

from n26_sharp_radius_constraints import tighten
import n26_quadratic_energy_minorant as energy
from verify_selected_type_trees import independently_contract


def split(node, lower, upper, total):
    if set(node) != {"kind", "axis", "mid", "children"}:
        raise ValueError("quadratic split has unknown fields")
    axis, middle, children = node["axis"], F(node["mid"]), node["children"]
    if (type(axis) is not int or not 0 <= axis < len(lower)
            or not lower[axis] < middle < upper[axis]
            or not isinstance(children, list) or len(children) != 2 or children[0] == children[1]
            or any(type(i) is not int or not 0 <= i < total for i in children)):
        raise ValueError("quadratic split loses a closed half or has an invalid midpoint")
    left_upper, right_lower = list(upper), list(lower)
    left_upper[axis], right_lower[axis] = middle, middle
    return ((children[0], list(lower), left_upper), (children[1], right_lower, list(upper)))


def independent_leaves(matrix, root_box, nodes):
    queue = deque([(0, list(map(F, root_box["lower"])), list(map(F, root_box["upper"])))])
    seen, leaves = set(), []
    while queue:
        index, lower, upper = queue.popleft()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("independent quadratic forest repeats or hides a node")
        seen.add(index)
        node = nodes[index]
        box = independently_contract(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("independent contracted empty box was not EMPTY")
            leaves.append({"index": index, "kind": "EMPTY"})
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            queue.extend(split(node, lower, upper, len(nodes)))
        elif node["kind"] in ("OPEN", "QUADRATIC_ENERGY"):
            leaves.append({"index": index, "kind": node["kind"],
                           "lower": list(map(str, lower)), "upper": list(map(str, upper))})
        else:
            raise ValueError("independent nonempty quadratic forest has invalid leaf kind")
    if len(seen) != len(nodes):
        raise ValueError("independent quadratic forest has unreachable nodes")
    return sorted(leaves, key=lambda row: row["index"])


def replay(spec, matrix, root_box, nodes, kernels, radius, arcs):
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("empty quadratic forest node list")
    stack = [(0, list(map(F, root_box["lower"])), list(map(F, root_box["upper"])), 0)]
    seen, pending, ledger, leaves = set(), [], [], []
    counts = dict.fromkeys(("SPLIT", "QUADRATIC_ENERGY", "EMPTY", "OPEN"), 0)
    depth, margins = 0, []
    while stack:
        index, lower, upper, level = stack.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("quadratic forest repeats or loses a node")
        seen.add(index)
        depth = max(depth, level)
        node = nodes[index]
        if not isinstance(node, dict) or node.get("kind") not in counts:
            raise ValueError("invalid quadratic forest node")
        counts[node["kind"]] += 1
        box = tighten(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("empty contracted forest box must be paid as EMPTY")
            row = {"index": index, "kind": "EMPTY"}
            leaves.append(row)
            ledger.append(row)
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            children = split(node, lower, upper, len(nodes))
            stack.extend((*child, level + 1) for child in reversed(children))
            continue
        row = {"index": index, "kind": node["kind"],
               "lower": list(map(str, lower)), "upper": list(map(str, upper))}
        leaves.append(row)
        if node["kind"] == "OPEN":
            if node != {"kind": "OPEN"}:
                raise ValueError("quadratic OPEN has unverified fields")
            pending.append(row)
        elif node["kind"] == "QUADRATIC_ENERGY":
            if set(node) != {"kind", "kernel_index", "certificate"}:
                raise ValueError("quadratic energy leaf has unverified fields")
            k = node["kernel_index"]
            if type(k) is not int or not 0 <= k < len(kernels) or kernels[k]["spec"] != spec:
                raise ValueError("quadratic leaf used a different full graph")
            result = energy.bound(kernels[k], matrix, lower, upper, node["certificate"], radius, arcs)
            if (not result["radius_at_most_Rstar_whole_box_excluded"]
                    or F(result["minimum_strict_radius_margin"]) <= 0):
                raise ValueError("quadratic forest payment is not strict on the whole leaf")
            margins.append(F(result["minimum_strict_radius_margin"]))
            ledger.append({**row, "kernel_index": k, "certificate": node["certificate"], **result})
        else:
            raise ValueError("nonempty forest leaf falsely declared EMPTY")
    if len(seen) != len(nodes):
        raise ValueError("quadratic forest contains hidden nodes")
    actual = sorted(leaves, key=lambda row: row["index"])
    if actual != independent_leaves(matrix, root_box, nodes):
        raise ValueError("independent BFS/DFS quadratic closed leaf boxes disagree")
    pending.sort(key=lambda row: row["index"])
    ledger.sort(key=lambda row: row["index"])
    result = {"nodes": len(nodes), "counts": counts, "maximum_depth": depth,
              "source_entire_closed_OPEN_box_partitioned": True,
              "independent_BFS_DFS_leaf_boxes_matched": True,
              "source_OPEN_box_fully_excluded": not pending,
              "unresolved_closed_boxes": len(pending),
              "minimum_strict_radius_margin": str(min(margins)) if margins else None}
    return result, pending, ledger
