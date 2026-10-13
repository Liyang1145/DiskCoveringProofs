"""Exact complete angular-box trees for N26 partial rod graphs."""

from fractions import Fraction as F

from n26_force import angular_domain, force_check, load_trig, rootbox, tighten


def verify_angular_tree(spec, nodes, arcs=None):
    if type(nodes) is not list or not nodes:
        raise ValueError("missing angular tree")
    arcs = arcs or load_trig()[0]
    matrix = angular_domain(spec)
    lower, upper = rootbox(matrix)
    stack = [(0, lower, upper, 0)]
    seen = set()
    counts = {"SPLIT": 0, "FORCE": 0, "EMPTY": 0}
    margins, depth_max = [], 0
    while stack:
        index, lower, upper, depth = stack.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("angular tree cyclic, repeated or invalid")
        seen.add(index)
        depth_max = max(depth_max, depth)
        node = nodes[index]
        if type(node) is not dict or node.get("kind") not in counts:
            raise ValueError("unproved/open angular leaf")
        kind = node["kind"]
        counts[kind] += 1
        box = tighten(matrix, lower, upper)
        if kind == "EMPTY":
            if set(node) != {"kind"} or box is not None:
                raise ValueError("nonempty angular box falsely called empty")
            continue
        if box is None:
            raise ValueError("nonempty angular node has an empty incoming domain")
        lower, upper = box
        if kind == "FORCE":
            if set(node) != {"kind", "cert"}:
                raise ValueError("malformed angular force leaf")
            result = force_check(spec, lower, upper, node["cert"], arcs)
            margin = F(result["strict_margin_above_U"])
            if margin <= 0:
                raise ValueError("angular force leaf is not strict")
            margins.append(margin)
        else:
            if set(node) != {"kind", "axis", "mid", "children"}:
                raise ValueError("malformed angular split")
            axis, children, mid = node["axis"], node["children"], F(node["mid"])
            if (type(axis) is not int or not 0 <= axis < spec["B"] - 1
                    or not lower[axis] < mid < upper[axis]
                    or type(children) is not list or len(children) != 2
                    or children[0] == children[1]
                    or any(type(k) is not int or not index < k < len(nodes) for k in children)):
                raise ValueError("angular split loses a closed half-box")
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis] = mid
            right_lower[axis] = mid
            stack.append((children[1], right_lower, list(upper), depth + 1))
            stack.append((children[0], list(lower), left_upper, depth + 1))
    if len(seen) != len(nodes) or counts["SPLIT"] + 1 != counts["FORCE"] + counts["EMPTY"]:
        raise ValueError("angular tree has unreachable or missing nodes")
    return {"nodes": len(nodes), "counts": counts, "max_depth": depth_max,
            "all_incoming_angular_boxes_covered": True,
            "minimum_strict_force_margin": str(min(margins)) if margins else None}
