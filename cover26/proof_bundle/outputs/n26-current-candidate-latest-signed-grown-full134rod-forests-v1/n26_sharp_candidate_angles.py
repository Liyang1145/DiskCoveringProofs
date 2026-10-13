"""Exact partial angular classification of the complete candidate transport.

Every necessary angle is assigned to a proved FORCE/LOCAL/EMPTY leaf or an
explicit OPEN leaf. OPEN is never accepted as a lower-bound certificate.
"""

from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import angular_domain, rootbox, tighten
from n26_direct_arc_force import force_check
import verify_anchor_pinning as pin


KINDS = ("SPLIT", "FORCE", "LOCAL", "EMPTY", "OPEN")


def input_gate(stress_folder, local_folder, transport_folder, pin_folder, proposal=None):
    pin_report, inventory = pin.checked_bundle(pin_folder)
    for path, digest in pin_report["source_files"].items():
        if pin.sha(path) != digest:
            raise ValueError("changed accepted pinning source")
        inventory.append(pin.local_path(path))
    if pin.sha(pin.__file__) != pin_report["files"]["verify_anchor_pinning.py"]:
        raise ValueError("sharp tree imported a different pinning checker")
    pin_proposal = json.loads((pin_folder / "CERTIFICATE.json").read_text())
    data = pin.source_gate(stress_folder, local_folder, transport_folder, pin_proposal)
    inventory.extend(data[-1])
    result = pin.derive(*data[:5], pin_proposal)
    if any(pin_report[key] != value for key, value in result.items()):
        raise ValueError("pinning source does not replay")
    path_data = data[3]
    final = path_data["states"][-1]
    if not final["terminal"] or final["next"] != 26 or len(final["faces"]) != 34:
        raise ValueError("candidate full transport is missing")
    spec = {"N": 26, "B": 16, "next": 26, "faces": final["faces"]}
    stress = json.loads((stress_folder / "VERIFIED.json").read_text())
    radius_upper = F(stress["modified_root_check"]["r_strict_interval"][1])
    sources = {
        "stress": pin.sha(stress_folder / "VERIFIED.json"),
        "local": pin.sha(local_folder / "VERIFIED.json"),
        "transport": pin.sha(transport_folder / "VERIFIED.json"),
        "pinning": pin.sha(pin_folder / "VERIFIED.json"),
    }
    if proposal is not None and (
        proposal["source_acceptance_sha256"] != sources
        or proposal["spec"] != spec
        or proposal["radius_scope"] != "same-root-Rstar"
    ):
        raise ValueError("sharp angular proposal changed its graph, root, or accepted sources")
    cells = [tuple(map(F, row)) for row in pin_proposal["closed_anchor_angle_cells"]]
    return spec, radius_upper, cells, sources, inventory


def replay(spec, radius_upper, cells, nodes, arcs):
    if type(nodes) is not list or not nodes:
        raise ValueError("missing sharp candidate angular tree")
    matrix = angular_domain(spec)
    lower, upper = rootbox(matrix)
    stack = [(0, lower, upper, 0)]
    seen, counts, pending, ledger, margins = set(), dict.fromkeys(KINDS, 0), [], [], []
    depth_max = 0
    while stack:
        index, lower, upper, depth = stack.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("sharp tree cyclic, repeated, or invalid")
        seen.add(index)
        depth_max = max(depth_max, depth)
        node = nodes[index]
        if type(node) is not dict or node.get("kind") not in KINDS:
            raise ValueError("unknown/unproved sharp node")
        kind = node["kind"]
        counts[kind] += 1
        box = tighten(matrix, lower, upper)
        if kind == "EMPTY":
            if set(node) != {"kind"} or box is not None:
                raise ValueError("nonempty sharp angular box falsely excluded")
            ledger.append({"index": index, "kind": kind})
            continue
        if box is None:
            raise ValueError("nonempty sharp node has an empty incoming domain")
        lower, upper = box
        if kind == "SPLIT":
            if set(node) != {"kind", "axis", "mid", "children"}:
                raise ValueError("malformed sharp angular split")
            axis, mid, children = node["axis"], F(node["mid"]), node["children"]
            if (type(axis) is not int or not 0 <= axis < 15
                    or not lower[axis] < mid < upper[axis]
                    or type(children) is not list or len(children) != 2
                    or children[0] == children[1]
                    or any(type(k) is not int or not index < k < len(nodes) for k in children)):
                raise ValueError("sharp split loses a closed half-box")
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis], right_lower[axis] = mid, mid
            stack.append((children[1], right_lower, list(upper), depth + 1))
            stack.append((children[0], list(lower), left_upper, depth + 1))
            continue
        row = {"index": index, "kind": kind, "depth": depth,
               "lower": list(map(str, lower)), "upper": list(map(str, upper))}
        if kind == "FORCE":
            if set(node) != {"kind", "cert"}:
                raise ValueError("malformed sharp force leaf")
            result = force_check(spec, lower, upper, node["cert"], arcs)
            margin = F(result["required_radius_lower"]) - radius_upper
            if margin <= 0:
                raise ValueError("force leaf does not exceed certified sharp root upper endpoint")
            margins.append(margin)
            ledger.append({**row, **result, "strict_margin_above_Rstar_upper": str(margin)})
        elif kind == "LOCAL":
            if set(node) != {"kind"} or any(
                not a <= lo <= hi <= b for lo, hi, (a, b) in zip(lower, upper, cells)
            ):
                raise ValueError("local leaf has not been geometrically pinned into accepted local box")
            ledger.append({**row, "radius_at_least_same_root_Rstar": True,
                           "equality_only_candidate_rotations_for_actual_covers": True})
        elif kind == "OPEN":
            if set(node) != {"kind"}:
                raise ValueError("malformed unresolved sharp box")
            pending.append(row)
        else:
            raise ValueError("invalid sharp angular leaf")
    if (len(seen) != len(nodes)
            or counts["SPLIT"] + 1 != sum(counts[k] for k in KINDS if k != "SPLIT")):
        raise ValueError("sharp angular partition has unreachable or missing nodes")
    return {
        "nodes": len(nodes), "counts": counts, "maximum_depth": depth_max,
        "entire_necessary_root_angle_domain_partitioned_including_boundaries": True,
        "unresolved_closed_angle_boxes": len(pending),
        "all_necessary_candidate_angles_lower_bounded": not pending,
        "candidate_transport_global_lower_bound_proved": not pending,
        "minimum_strict_force_margin_above_Rstar_upper": str(min(margins)) if margins else None,
        "local_leaf_uses_nonlocal_pinning_not_assumed_center_closeness": bool(counts["LOCAL"]),
    }, pending, ledger


def seeded_partition(spec, cells):
    """Extract the accepted local patch using all closed slab complements."""
    matrix = angular_domain(spec)
    lower, upper = rootbox(matrix)
    nodes, pending, inside = [{"kind": "OPEN"}], [], 0
    for axis, (lo, hi) in enumerate(cells):
        for cut, inside_side in ((lo, 1), (hi, 0)):
            box = tighten(matrix, lower, upper)
            if box is None:
                raise ValueError("known candidate local patch lost during extraction")
            lower, upper = box
            if (inside_side == 1 and lower[axis] >= cut) or (inside_side == 0 and upper[axis] <= cut):
                continue
            if not lower[axis] < cut < upper[axis]:
                raise ValueError("pinning patch lies outside required root domain")
            children = [len(nodes), len(nodes) + 1]
            nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
            nodes[inside] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": children}
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis], right_lower[axis] = cut, cut
            sides = ((children[0], list(lower), left_upper),
                     (children[1], right_lower, list(upper)))
            pending.append(sides[1 - inside_side])
            inside, lower, upper = sides[inside_side]
    nodes[inside] = {"kind": "LOCAL"}
    return nodes, pending
