"""Closed U-domain partitions with radius-conditional sharp leaves."""

from fractions import Fraction as F

from n26_force import angular_domain, rootbox, tighten
from n26_direct_arc_force import force_check
import n26_sharp_radius_constraints as sharp


KINDS = ("SPLIT", "FORCE", "LOCAL", "EMPTY", "OPEN",
         "SHARP_FORCE", "SHARP_LOCAL", "SHARP_EMPTY")


def replay(spec, radius_upper, pin_cells, sharp_matrix, nodes, arcs):
    if type(nodes) is not list or not nodes:
        raise ValueError("missing sharp-constraint angular tree")
    old_matrix = angular_domain(spec)
    lower, upper = rootbox(old_matrix)
    stack = [(0, lower, upper, 0)]
    seen, counts, pending, ledger, margins = set(), dict.fromkeys(KINDS, 0), [], [], []
    depth_max = 0
    while stack:
        index, lower, upper, depth = stack.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("sharp-constraint tree cyclic, repeated or invalid")
        seen.add(index)
        depth_max = max(depth_max, depth)
        node = nodes[index]
        if type(node) is not dict or node.get("kind") not in KINDS:
            raise ValueError("unknown sharp-constraint tree node")
        kind = node["kind"]
        counts[kind] += 1
        old_box = tighten(old_matrix, lower, upper)
        if kind == "EMPTY":
            if set(node) != {"kind"} or old_box is not None:
                raise ValueError("sharp infeasibility falsely called original-domain emptiness")
            ledger.append({"index": index, "kind": kind})
            continue
        if old_box is None:
            raise ValueError("nonempty sharp node has empty original incoming domain")
        lower, upper = old_box
        if kind == "SPLIT":
            if set(node) != {"kind", "axis", "mid", "children"}:
                raise ValueError("malformed sharp continuation split")
            axis, middle, children = node["axis"], F(node["mid"]), node["children"]
            if (type(axis) is not int or not 0 <= axis < spec["B"] - 1
                    or not lower[axis] < middle < upper[axis]
                    or type(children) is not list or len(children) != 2
                    or children[0] == children[1]
                    or any(type(k) is not int or not index < k < len(nodes) for k in children)):
                raise ValueError("sharp continuation loses an original closed half-box")
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis], right_lower[axis] = middle, middle
            stack.append((children[1], right_lower, list(upper), depth + 1))
            stack.append((children[0], list(lower), left_upper, depth + 1))
            continue
        row = {"index": index, "kind": kind, "depth": depth,
               "lower": list(map(str, lower)), "upper": list(map(str, upper))}
        narrowed = sharp.tighten(sharp_matrix, lower, upper)
        if kind == "SHARP_EMPTY":
            if set(node) != {"kind"} or narrowed is not None:
                raise ValueError("nonempty sharp-radius domain falsely excluded")
            ledger.append({**row, "radius_at_most_Rstar_infeasible": True,
                           "does_not_claim_original_U_box_empty": True})
            continue
        if kind.startswith("SHARP_"):
            if narrowed is None:
                raise ValueError("paid sharp leaf has no sharp domain")
            effective_lower, effective_upper = narrowed
            row.update({"sharp_lower": list(map(str, effective_lower)),
                        "sharp_upper": list(map(str, effective_upper))})
        else:
            effective_lower, effective_upper = lower, upper
        if kind in ("FORCE", "SHARP_FORCE"):
            if set(node) != {"kind", "cert"}:
                raise ValueError("malformed sharp-radius force leaf")
            result = force_check(spec, effective_lower, effective_upper, node["cert"], arcs)
            margin = F(result["required_radius_lower"]) - radius_upper
            if margin <= 0:
                raise ValueError("sharp-radius force lower bound is not strict")
            margins.append(margin)
            ledger.append({**row, **result, "strict_margin_above_Rstar_upper": str(margin),
                           "uses_radius_conditional_sharp_constraints": kind == "SHARP_FORCE"})
        elif kind in ("LOCAL", "SHARP_LOCAL"):
            if set(node) != {"kind"} or any(not a <= lo <= hi <= b
                    for lo, hi, (a, b) in zip(effective_lower, effective_upper, pin_cells)):
                raise ValueError("sharp local leaf not fully in accepted nonlocal pinning box")
            ledger.append({**row, "radius_at_least_same_root_Rstar": True,
                           "uses_radius_conditional_sharp_constraints": kind == "SHARP_LOCAL"})
        elif kind == "OPEN":
            if set(node) != {"kind"}:
                raise ValueError("malformed retained sharp OPEN")
            if narrowed is None:
                row["sharp_radius_domain_empty"] = True
            else:
                row["sharp_radius_domain_empty"] = False
                row["sharp_lower"], row["sharp_upper"] = list(map(str, narrowed[0])), list(map(str, narrowed[1]))
                row["sharp_radius_domain_inside_local"] = all(
                    a <= lo <= hi <= b for lo, hi, (a, b) in zip(narrowed[0], narrowed[1], pin_cells))
            pending.append(row)
        else:
            raise ValueError("invalid sharp leaf kind")
    if len(seen) != len(nodes) or counts["SPLIT"] + 1 != sum(counts[k] for k in KINDS if k != "SPLIT"):
        raise ValueError("sharp tree has unreachable or missing nodes")
    return {
        "nodes": len(nodes), "counts": counts, "maximum_depth": depth_max,
        "entire_original_U_necessary_angle_domain_partitioned_with_all_closed_boundaries": True,
        "sharp_leaf_scope_is_radius_at_most_Rstar_not_unconditional_U_emptiness": True,
        "unresolved_closed_angle_boxes": len(pending),
        "all_radius_at_most_Rstar_candidate_domains_lower_bounded": not pending,
        "candidate_transport_global_lower_bound_proved": not pending,
        "minimum_strict_force_margin_above_Rstar_upper": str(min(margins)) if margins else None,
    }, pending, ledger
