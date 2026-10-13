"""Exact closed necessary angle trees, conditional on radius at most Rstar."""

from fractions import Fraction as F

from n26_sharp_radius_constraints import SCALE, tighten
from n26_direct_arc_force import force_check as direct_check
from n26_correlated_arc_force import force_check as correlated_check


def rootbox(matrix):
    return ([F(-matrix[i][0], SCALE) for i in range(1, len(matrix))],
            [F(matrix[0][i], SCALE) for i in range(1, len(matrix))])


def replay(spec, matrix, radius_upper, nodes, arcs):
    lower, upper = rootbox(matrix)
    stack, seen, pending, ledger, margins = [(0, lower, upper)], set(), [], [], []
    counts = dict.fromkeys(("SPLIT", "DIRECT_FORCE", "CORRELATED_FORCE", "EMPTY", "OPEN"), 0)
    while stack:
        index, lower, upper = stack.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("sharp type tree cyclic, repeated or invalid")
        seen.add(index)
        node = nodes[index]
        if not isinstance(node, dict) or node.get("kind") not in counts:
            raise ValueError("unknown sharp type node")
        kind = node["kind"]
        counts[kind] += 1
        box = tighten(matrix, lower, upper)
        if kind == "EMPTY":
            if set(node) != {"kind"} or box is not None:
                raise ValueError("nonempty sharp necessary box falsely excluded")
            ledger.append({"index": index, "kind": kind})
            continue
        if box is None:
            raise ValueError("paid or retained nonempty type node has empty domain")
        lower, upper = box
        if kind == "SPLIT":
            if set(node) != {"kind", "axis", "mid", "children"}:
                raise ValueError("malformed sharp type split")
            axis, middle, children = node["axis"], F(node["mid"]), node["children"]
            if (type(axis) is not int or not 0 <= axis < spec["B"] - 1
                    or not lower[axis] < middle < upper[axis]
                    or not isinstance(children, list) or len(children) != 2 or children[0] == children[1]
                    or any(type(k) is not int or not index < k < len(nodes) for k in children)):
                raise ValueError("sharp type split lost a closed half")
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis], right_lower[axis] = middle, middle
            stack.extend(((children[1], right_lower, list(upper)),
                          (children[0], list(lower), left_upper)))
            continue
        row = {"index": index, "kind": kind, "lower": list(map(str, lower)), "upper": list(map(str, upper))}
        if kind == "OPEN":
            if set(node) != {"kind"}:
                raise ValueError("malformed retained type OPEN")
            pending.append(row)
            continue
        if set(node) != {"kind", "cert"}:
            raise ValueError("malformed strict type force leaf")
        value = (direct_check(spec, lower, upper, node["cert"], arcs) if kind == "DIRECT_FORCE"
                 else correlated_check(spec, lower, upper, matrix, node["cert"], arcs))
        margin = F(value["required_radius_lower"]) - radius_upper
        if margin <= 0:
            raise ValueError("type force is not strictly above the certified root upper endpoint")
        margins.append(margin)
        ledger.append({**row, **value, "strict_margin_above_Rstar_upper": str(margin)})
    if len(seen) != len(nodes) or counts["SPLIT"] + 1 != sum(value for kind, value in counts.items() if kind != "SPLIT"):
        raise ValueError("sharp type tree has unreachable or missing nodes")
    return {"nodes": len(nodes), "counts": counts, "radius_at_most_Rstar_type_excluded": not pending,
            "unresolved_closed_boxes": len(pending),
            "minimum_strict_margin": str(min(margins)) if margins else None}, pending, ledger
