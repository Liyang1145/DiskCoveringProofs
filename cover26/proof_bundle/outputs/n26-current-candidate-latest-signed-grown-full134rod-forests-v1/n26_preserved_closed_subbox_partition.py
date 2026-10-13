"""Isolate a contained closed subbox by fresh splits of actual OPEN nodes.

This function proves no energy bound and assigns no new proof kind. It leaves
the target and all nonempty remainders OPEN for a caller's fresh arithmetic.
No old nonOPEN node is overwritten, and no source/history cache is imported.
"""

from copy import deepcopy
from fractions import Fraction as F

import n26_mixed_full134rod_support_forest as mixed


def isolate(matrix, row, nodes, open_index, target_lower, target_upper):
    if type(open_index) is not int or not 0 <= open_index < len(nodes):
        raise ValueError("closed subbox target is not an actual forest node")
    if nodes[open_index] != {"kind": "OPEN"}:
        raise ValueError("closed subbox refinement would overwrite an old nonOPEN proof")
    dfs = mixed.partition(matrix, row, nodes, mixed.old.prior.prior.tighten, False)
    bfs = mixed.partition(matrix, row, nodes, mixed.old.prior.prior.independently_contract, True)
    if dfs != bfs:
        raise ValueError("closed subbox seed independent partitions disagree")
    leaves = {leaf["index"]: leaf for leaf in dfs}
    if open_index not in leaves or leaves[open_index]["kind"] != "OPEN":
        raise ValueError("closed subbox target is not an actual reachable OPEN leaf")
    leaf = leaves[open_index]
    lower, upper = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    a, b = list(map(F, target_lower)), list(map(F, target_upper))
    if (len(a) != len(lower) or len(b) != len(upper)
            or any(not l <= x <= y <= u for l, u, x, y in zip(lower, upper, a, b))
            or (a == lower and b == upper)):
        raise ValueError("closed subbox is not an actual proper contained closed domain")
    target = mixed.old.prior.prior.tighten(matrix, a, b)
    independent = mixed.old.prior.prior.independently_contract(matrix, a, b)
    if target is None or target != independent:
        raise ValueError("closed subbox is empty or did not contract independently")
    a, b = target
    new_nodes, cursor, decisions = deepcopy(nodes), open_index, []
    contractor = mixed.old.prior.prior.tighten

    def split(axis, cut, side, lower, upper):
        nonlocal cursor
        if not lower[axis] < cut < upper[axis]:
            raise ValueError("closed subbox needs an unsupported boundary-only cut")
        children = [len(new_nodes), len(new_nodes)+1]
        new_nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
        new_nodes[cursor] = {"kind": "SPLIT", "axis": axis, "mid": str(cut), "children": children}
        left_upper, right_lower = list(upper), list(lower)
        left_upper[axis], right_lower[axis] = cut, cut
        left = contractor(matrix, lower, left_upper)
        right = contractor(matrix, right_lower, upper)
        if left != mixed.old.prior.prior.independently_contract(matrix, lower, left_upper):
            raise ValueError("closed subbox left half failed independent contraction")
        if right != mixed.old.prior.prior.independently_contract(matrix, right_lower, upper):
            raise ValueError("closed subbox right half failed independent contraction")
        for child, box in zip(children, (left, right)):
            if box is None:
                new_nodes[child] = {"kind": "EMPTY"}
        chosen = (left, right)[side]
        if chosen is None:
            raise ValueError("closed subbox refinement lost its contained target")
        decisions.append({"old_OPEN_node": cursor, "axis": axis, "closed_shared_cut": str(cut),
                          "children": children, "target_side": side,
                          "both_closed_halves_and_all_nonempty_remainders_retained": True})
        cursor = children[side]
        return chosen

    for axis in range(len(a)):
        if a[axis] > lower[axis]:
            lower, upper = split(axis, a[axis], 1, lower, upper)
        if b[axis] < upper[axis]:
            lower, upper = split(axis, b[axis], 0, lower, upper)
    if (any(not x <= l <= u <= y for x, y, l, u in zip(a, b, lower, upper))
            or any(node["kind"] != "OPEN" and node != new_nodes[index]
                   for index, node in enumerate(nodes))):
        raise ValueError("closed subbox refinement changed an old proof or missed exact containment")
    actual_dfs = mixed.partition(matrix, row, new_nodes, contractor, False)
    actual_bfs = mixed.partition(matrix, row, new_nodes, mixed.old.prior.prior.independently_contract, True)
    if actual_dfs != actual_bfs:
        raise ValueError("closed subbox final shared-boundary partition did not agree")
    actual = next(leaf for leaf in actual_dfs if leaf["index"] == cursor)
    if (actual["kind"] != "OPEN" or list(map(F, actual["lower"])) != lower
            or list(map(F, actual["upper"])) != upper):
        raise ValueError("closed subbox actual isolated OPEN domain changed")
    return new_nodes, cursor, actual, decisions
