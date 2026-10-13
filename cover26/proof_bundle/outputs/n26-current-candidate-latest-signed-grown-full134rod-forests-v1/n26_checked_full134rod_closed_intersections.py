"""Fresh exact intersections of checked regions with a preserved OPEN cover.

Pure arithmetic only. This does not select a source, load an old diagnosis,
grant ownership, or turn a partial forest into a geometric payment.
"""

from copy import deepcopy
from fractions import Fraction as F

import n26_preserved_closed_subbox_partition as cutter


mixed = cutter.mixed


def intersection(matrix, leaf, lower, upper):
    a, b = list(map(F, lower)), list(map(F, upper))
    lo, hi = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    if (len(a) != len(lo) or len(b) != len(hi)
            or any(x > y for x, y in zip(a, b))):
        raise ValueError("checked closed intersection has invalid region dimensions")
    left = [max(x, y) for x, y in zip(lo, a)]
    right = [min(x, y) for x, y in zip(hi, b)]
    if any(x > y for x, y in zip(left, right)):
        return None
    actual = mixed.old.prior.prior.tighten(matrix, left, right)
    independent = mixed.old.prior.prior.independently_contract(matrix, left, right)
    if actual != independent:
        raise ValueError("checked closed intersection did not contract independently")
    return actual


def refine(original, arcs, row, seed_nodes, kernels, regions, max_targets=64,
           progress=None):
    if type(max_targets) is not int or not 1 <= max_targets <= 4096:
        raise ValueError("invalid bounded checked-intersection continuation")
    nodes, targets, decisions, scans = deepcopy(seed_nodes), [], [], []
    contractor = mixed.old.prior.prior.tighten
    for region_index, region in enumerate(regions):
        if set(region) != {"lower", "upper", "full_support_index", "certificate"}:
            raise ValueError("checked region has unknown proof or ownership fields")
        support_index = region["full_support_index"]
        if type(support_index) is not int or not 0 <= support_index < len(kernels):
            raise ValueError("checked region names an invalid distinct full134rod support")
        leaves = mixed.partition(original["matrix"], row, nodes, contractor, False)
        bfs = mixed.partition(
            original["matrix"], row, nodes,
            mixed.old.prior.prior.independently_contract, True)
        if leaves != bfs:
            raise ValueError("checked-intersection actual seed partitions disagree")
        scan = {"region_index": region_index, "actual_OPEN_regions_examined": 0,
                "disjoint": 0, "non_strict_retained_OPEN": 0,
                "unsupported_boundary_only_retained_OPEN": 0,
                "strict_whole_OPEN_leaves": 0, "strict_isolated_subboxes": 0,
                "target_limit_reached_with_all_remainders_retained": False}
        for leaf in leaves:
            if leaf["kind"] != "OPEN":
                continue
            if len(targets) >= max_targets:
                scan["target_limit_reached_with_all_remainders_retained"] = True
                break
            if nodes[leaf["index"]] != {"kind": "OPEN"}:
                raise ValueError("checked intersection would reset a nonOPEN proof")
            scan["actual_OPEN_regions_examined"] += 1
            box = intersection(
                original["matrix"], leaf, region["lower"], region["upper"])
            if box is None:
                scan["disjoint"] += 1
                continue
            result = mixed.correlated.bound(
                kernels[support_index], original["matrix"], *box,
                region["certificate"], original["radius"], arcs)
            if not result["arithmetic_strict_target_test_passed"]:
                scan["non_strict_retained_OPEN"] += 1
                continue
            lo, hi = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
            whole = box == (lo, hi)
            cuts = []
            if whole:
                target_index, actual = leaf["index"], leaf
                next_nodes = nodes
            else:
                # A zero-width slice may not be isolated by two strict
                # interior closed cuts. Keep its whole source OPEN in that
                # case; do not silently discard a shared boundary.
                if any(a == b and x != y for a, b, x, y in zip(*box, lo, hi)):
                    scan["unsupported_boundary_only_retained_OPEN"] += 1
                    continue
                next_nodes, target_index, actual, cuts = cutter.isolate(
                    original["matrix"], row, nodes, leaf["index"], *box)
            fresh = mixed.correlated.bound(
                kernels[support_index], original["matrix"],
                actual["lower"], actual["upper"], region["certificate"],
                original["radius"], arcs)
            if not fresh["arithmetic_strict_target_test_passed"]:
                raise ValueError("actual whole isolated target lost its fresh strict bound")
            next_nodes[target_index] = {
                "kind": mixed.KIND, "full_support_index": support_index,
                "certificate": deepcopy(region["certificate"]),
            }
            nodes = next_nodes
            decisions.extend(cuts)
            targets.append({
                "region_index": region_index,
                "source_actual_OPEN_leaf": deepcopy(leaf),
                "actual_target_index": target_index,
                "whole_source_OPEN_leaf": whole,
                "actual_closed_lower": actual["lower"],
                "actual_closed_upper": actual["upper"],
                "full_support_index": support_index,
                "fresh_exact_whole_closed_target_result": fresh,
            })
            scan["strict_whole_OPEN_leaves" if whole else "strict_isolated_subboxes"] += 1
            if progress is not None:
                progress(targets[-1], len(targets))
        scans.append(scan)
    if any(node["kind"] != "OPEN" and node != nodes[index]
           for index, node in enumerate(seed_nodes)):
        raise ValueError("checked intersections changed a previously proved nonOPEN node")
    return nodes, targets, decisions, scans
