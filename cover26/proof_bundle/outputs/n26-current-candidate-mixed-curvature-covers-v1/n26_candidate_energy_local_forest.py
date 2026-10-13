"""Closed-half candidate energy/LOCAL forests on the original 92-rod frame.

LOCAL discharges a radius-lower-bound obligation; it does not declare an
equality-feasible region empty. Every source root and shared split boundary
is reconstructed independently.
"""

from collections import deque
from copy import deepcopy
from fractions import Fraction as F

import n26_candidate_curvature_energy as energy
from n26_sharp_radius_constraints import tighten
from verify_selected_type_trees import independently_contract
import verify_candidate_curvature_overlay as source


KINDS = ("SPLIT", "ENERGY", "LOCAL", "EMPTY", "OPEN")


def split(node, index, lower, upper, total):
    if set(node) != {"kind", "axis", "mid", "children"}:
        raise ValueError("candidate closed split has unknown fields")
    axis, mid, children = node["axis"], F(node["mid"]), node["children"]
    if (type(axis) is not int or not 0 <= axis < len(lower)
            or not lower[axis] < mid < upper[axis]
            or not isinstance(children, list) or len(children) != 2 or children[0] == children[1]
            or any(type(child) is not int or not index < child < total for child in children)):
        raise ValueError("candidate split loses a closed half or its shared midpoint")
    left_upper, right_lower = list(upper), list(lower)
    left_upper[axis], right_lower[axis] = mid, mid
    return ((children[0], list(lower), left_upper), (children[1], right_lower, list(upper)))


def local_proof(original, lower, upper):
    tiny = [tuple(map(F, row)) for row in original["cap"]["known_candidate_tiny_angle_cells"]]
    if len(lower) != 15 or len(upper) != 15:
        raise ValueError("candidate LOCAL leaf changed the original anchor frame")
    reference = deepcopy(original["reference"])
    hull = [[str(min(F(a), x)), str(max(F(b), y))]
            for a, b, (x, y) in zip(lower, upper, tiny)]
    reference["closed_anchor_angle_cells"] = hull
    pin = source.source.leaf.refined.derive(*original["data"][:5], reference)
    allowed = F(pin["accepted_local_box_original_coordinate_halfwidth"])
    error = F(pin["maximum_center_to_exact_rotated_root_euclidean_error_upper"])
    if allowed != F(7, 800000) or not error < allowed:
        raise ValueError("whole actual candidate leaf/root hull does not enter the original local barrier")
    return {"root_containing_closed_hull": hull,
            "all_actual_leaf_corners_and_feasible_root_cells_in_hull": True,
            "original_52_coordinate_local_allowance": str(allowed),
            "original_LOCAL_maximum_center_error_upper": str(error),
            "strict_original_LOCAL_entry_margin": str(allowed - error),
            "radius_at_least_same_root_Rstar": True,
            "candidate_equality_region_not_declared_empty": True,
            "original_leaf_specific_pinning": pin}


def independent_leaves(matrix, row, nodes):
    queue = deque([(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])))])
    seen, leaves = set(), []
    while queue:
        index, lower, upper = queue.popleft()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("independent candidate forest hides or repeats a node")
        seen.add(index)
        node = nodes[index]
        box = independently_contract(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("independent empty candidate domain was not EMPTY")
            leaves.append({"index": index, "kind": "EMPTY"})
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            queue.extend(split(node, index, lower, upper, len(nodes)))
        elif node["kind"] in ("ENERGY", "LOCAL", "OPEN"):
            leaves.append({"index": index, "kind": node["kind"],
                           "lower": list(map(str, lower)), "upper": list(map(str, upper))})
        else:
            raise ValueError("independent candidate forest has an invalid nonempty leaf")
    if len(seen) != len(nodes):
        raise ValueError("independent candidate forest has unreachable nodes")
    return sorted(leaves, key=lambda leaf: leaf["index"])


def replay(original, kernel, arcs, row, nodes):
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("candidate source root lacks its complete forest")
    stack = [(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])), 0)]
    matrix, radius = original["matrix"], original["radius"]
    seen, leaves, pending, ledger = set(), [], [], []
    counts = dict.fromkeys(KINDS, 0)
    depth, energy_margins, local_margins = 0, [], []
    while stack:
        index, lower, upper, level = stack.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("candidate forest repeats, hides or loses a node")
        seen.add(index)
        node = nodes[index]
        if not isinstance(node, dict) or node.get("kind") not in KINDS:
            raise ValueError("unknown candidate forest node")
        counts[node["kind"]] += 1
        depth = max(depth, level)
        box = tighten(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("exact empty candidate domain must be EMPTY")
            leaf = {"index": index, "kind": "EMPTY"}
            leaves.append(leaf)
            ledger.append(leaf)
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            stack.extend((*child, level + 1) for child in reversed(split(node, index, lower, upper, len(nodes))))
            continue
        leaf = {"index": index, "kind": node["kind"],
                "lower": list(map(str, lower)), "upper": list(map(str, upper))}
        leaves.append(leaf)
        if node["kind"] == "OPEN":
            if node != {"kind": "OPEN"}:
                raise ValueError("candidate OPEN carries unverified proof fields")
            pending.append(leaf)
        elif node["kind"] == "ENERGY":
            if set(node) != {"kind", "certificate"}:
                raise ValueError("candidate energy leaf has unknown fields")
            result = energy.bound(kernel, matrix, lower, upper, node["certificate"], radius, arcs)
            energy.strict_gate(result)
            energy_margins.append(F(result["minimum_strict_radius_margin"]))
            ledger.append({**leaf, "certificate": node["certificate"], **result})
        elif node["kind"] == "LOCAL":
            if node != {"kind": "LOCAL"}:
                raise ValueError("candidate local hull must be reconstructed, not supplied")
            result = local_proof(original, lower, upper)
            local_margins.append(F(result["strict_original_LOCAL_entry_margin"]))
            ledger.append({**leaf, **result})
        else:
            raise ValueError("nonempty candidate leaf falsely declared EMPTY")
    if len(seen) != len(nodes) or counts["SPLIT"] + 1 != sum(counts[kind] for kind in KINDS if kind != "SPLIT"):
        raise ValueError("candidate forest has a hidden or omitted closed branch")
    actual = sorted(leaves, key=lambda leaf: leaf["index"])
    if actual != independent_leaves(matrix, row, nodes):
        raise ValueError("candidate independent BFS and exact DFS leaf domains disagree")
    pending.sort(key=lambda leaf: leaf["index"])
    ledger.sort(key=lambda leaf: leaf["index"])
    result = {"nodes": len(nodes), "counts": counts, "maximum_depth": depth,
              "entire_actual_source_closed_box_covered": True,
              "independent_BFS_DFS_closed_leaves_agreed": True,
              "source_candidate_root_fully_lower_bounded": not pending,
              "source_candidate_root_strictly_empty": not pending and counts["LOCAL"] == 0,
              "unresolved_closed_leaf_boxes": len(pending),
              "minimum_strict_energy_radius_margin": str(min(energy_margins)) if energy_margins else None,
              "minimum_strict_original_LOCAL_entry_margin": str(min(local_margins)) if local_margins else None,
              "original_52_coordinate_local_allowance_unchanged": "7/800000"}
    return result, pending, ledger
