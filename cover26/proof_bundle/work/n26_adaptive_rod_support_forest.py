"""Unadmitted complete closed partitions with DISTINCT original/new supports."""

from collections import deque
from fractions import Fraction as F

import n26_candidate_energy_local_forest as local
import n26_difference_product_curvature as product
import n26_dirichlet_energy as original_energy
import n26_reweighted_candidate_energy as alternative
from n26_sharp_radius_constraints import tighten
from verify_selected_type_trees import independently_contract


KINDS = ("SPLIT", "ORIGINAL-ENERGY", "PRODUCT-ENERGY",
         "ALTERNATIVE-ENERGY", "LOCAL", "EMPTY", "OPEN")


def partition(matrix, row, nodes, contractor, breadth_first):
    queue = deque([(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])))])
    seen, leaves = set(), []
    while queue:
        index, lower, upper = queue.popleft() if breadth_first else queue.pop()
        if type(index) is not int or not 0 <= index < len(nodes) or index in seen:
            raise ValueError("adaptive support forest hides or repeats a node")
        seen.add(index)
        node = nodes[index]
        if not isinstance(node, dict) or node.get("kind") not in KINDS:
            raise ValueError("adaptive support forest has an unknown proof mode")
        box = contractor(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("adaptive support exact empty region must be EMPTY")
            leaves.append({"index": index, "kind": "EMPTY"})
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            children = local.split(node, index, lower, upper, len(nodes))
            queue.extend(children if breadth_first else reversed(children))
        elif node["kind"] != "EMPTY":
            leaves.append({
                "index": index, "kind": node["kind"],
                "lower": list(map(str, lower)), "upper": list(map(str, upper))})
        else:
            raise ValueError("adaptive support nonempty region falsely called EMPTY")
    if len(seen) != len(nodes):
        raise ValueError("adaptive support forest has an unreachable hidden node")
    return sorted(leaves, key=lambda item: item["index"])


def support_gate(original, supports):
    if not isinstance(supports, list) or not 1 <= len(supports) <= 32:
        raise ValueError("adaptive support table is absent or excessive")
    kernels = []
    for item in supports:
        if (set(item) != {"mode", "reference", "inverse", "suggestion_point_turns"}
                or item["mode"] != "NEW-POSITIVE-SUPPORT"):
            raise ValueError("adaptive support table relabels an original or unknown kernel")
        kernel = alternative.kernel_gate(original["reference"], item["reference"], item["inverse"])
        point = list(map(F, item["suggestion_point_turns"]))
        if len(point) != 15:
            raise ValueError("adaptive support suggestion changed the anchor frame")
        # Suggestion points are DATA only; actual bounds depend solely on the
        # explicit checked positive weights and their exact inverse.
        kernels.append(kernel)
    return kernels


def direct_bound(kernel, lower, upper, radius, arcs):
    return original_energy.bound(lower, upper, kernel, F(radius)**2, arcs)


def replay(original, original_kernel, arcs, row, nodes, supports):
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("adaptive support forest has no entire-root partition")
    dfs = partition(original["matrix"], row, nodes, tighten, False)
    bfs = partition(original["matrix"], row, nodes, independently_contract, True)
    if dfs != bfs:
        raise ValueError("adaptive support BFS/DFS exact closed leaf domains disagree")
    kernels = support_gate(original, supports)
    counts = {kind: sum(node["kind"] == kind for node in nodes) for kind in KINDS}
    if counts["SPLIT"]+1 != len(dfs):
        raise ValueError("adaptive support forest lost a complete closed sibling")
    pending, ledger, margins, local_margins = [], [], [], []
    used_supports = set()
    for leaf in dfs:
        node, kind = nodes[leaf["index"]], leaf["kind"]
        if kind == "OPEN":
            if node != {"kind": "OPEN"}:
                raise ValueError("adaptive support OPEN leaf supplied unproved proof fields")
            pending.append(leaf)
            continue
        if kind == "EMPTY":
            ledger.append(leaf)
            continue
        if kind == "LOCAL":
            if node != {"kind": "LOCAL"}:
                raise ValueError("adaptive support LOCAL must use the freshly rebuilt original proof")
            result = local.local_proof(original, list(map(F, leaf["lower"])),
                                       list(map(F, leaf["upper"])))
            local_margins.append(F(result["strict_original_LOCAL_entry_margin"]))
            ledger.append({**leaf, "original_LOCAL_result": result})
            continue
        if kind == "PRODUCT-ENERGY":
            if set(node) != {"kind", "certificate"}:
                raise ValueError("adaptive original product leaf has unknown proof fields")
            result = product.bound(
                original_kernel, original["matrix"], leaf["lower"], leaf["upper"],
                node["certificate"], original["radius"], arcs)
            if (not result["arithmetic_strict_target_test_passed"]
                    or F(result["strict_radius_margin"]) <= 0):
                raise ValueError("adaptive original product leaf has no exact strict margin")
            margin = F(result["strict_energy_margin"])
            ledger.append({**leaf, "certificate": node["certificate"], "arithmetic_result": result})
        else:
            if kind == "ORIGINAL-ENERGY":
                if node != {"kind": kind}:
                    raise ValueError("adaptive original fixed-weight leaf has unknown proof fields")
                kernel = original_kernel
            else:
                if set(node) != {"kind", "support_index"}:
                    raise ValueError("adaptive alternative energy leaf has unknown proof fields")
                index = node["support_index"]
                if type(index) is not int or not 0 <= index < len(kernels):
                    raise ValueError("adaptive alternative leaf names an invalid positive support")
                used_supports.add(index)
                kernel = kernels[index]
            result = direct_bound(kernel, leaf["lower"], leaf["upper"], original["radius"], arcs)
            margin = F(result["strict_energy_exclusion_margin"])
            if not result["radius_conditional_whole_angle_box_excluded"] or margin <= 0:
                raise ValueError("adaptive direct energy leaf has no exact strict margin")
            ledger.append({**leaf, **({"support_index": node["support_index"]}
                                      if kind == "ALTERNATIVE-ENERGY" else {}),
                           "arithmetic_result": result})
        if margin <= 0:
            raise ValueError("adaptive energy arithmetic margin is not strictly positive")
        margins.append(margin)
    return {
        "nodes": len(nodes), "counts": counts,
        "entire_actual_source_closed_root_partition_checked": True,
        "independent_BFS_DFS_closed_domains_and_shared_boundaries_agreed": True,
        "all_new_positive_support_exact_inverses_and_original_rod_edges_checked": True,
        "alternative_supports_checked": len(kernels),
        "alternative_supports_used_by_strict_closed_leaves": sorted(used_supports),
        "arithmetic_entire_root_lower_bound_cover_completed": not pending,
        "arithmetic_entire_root_strictly_empty": not pending and counts["LOCAL"] == 0,
        "retained_OPEN_leaves": len(pending),
        "minimum_strict_energy_margin": str(min(margins)) if margins else None,
        "minimum_original_LOCAL_entry_margin": str(min(local_margins)) if local_margins else None,
        "original_52_coordinate_LOCAL_allowance_unchanged": "7/800000",
        "LOCAL_equality_regions_not_declared_empty": True,
        "original_fixed_kernel_and_NEW_positive_supports_distinctly_labelled": True,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_source_model_history_geometry_admission_still_required": True,
    }, pending, ledger
