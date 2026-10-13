"""Stdlib-only complete simple-hole recursion and independent branch-tree replay."""
from pathlib import Path
from itertools import combinations
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from complete_simple_collar import bits, simple_holes, budgets
from cross_order_strict_transfer import validate_disk
from eight_rod_angles import verify_cycle

assert __debug__


from general_collar_filling_linked import start_states, children

def all_complete_codes(N, B, centers, outer):
    """Control-only exhaustive reference on small fixed families."""
    from group_catalog import canonical_full
    stack, codes, calls = start_states(N, B, centers, outer), set(), 0
    while stack:
        state = stack.pop();calls += 1
        following = children(state, N, B)
        if following is None:
            codes.add(canonical_full(N, B, state["faces"]))
        else:
            stack.extend(following)
    return codes, calls


def replay(path, constants):
    """Reconstruct every child, verify every force, reject any missing branch."""
    payload = json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)
    assert payload["schema"] == "proof-paid-linked-general-collar-branch-tree-v1"
    N, B, centers, outer = (payload[k] for k in ("N", "B", "collar_centers", "collar_faces"))
    roots = start_states(N, B, centers, outer)
    nodes = payload["nodes"]
    assert len(payload["roots"]) == len(roots)
    work = list(zip(payload["roots"], roots, strict=True))
    visited = set()
    force = angles = pending_full = frontier = split = dead = 0
    from fractions import Fraction as F
    minimum = None
    while work:
        index, expected = work.pop()
        assert type(index) is int and 0 <= index < len(nodes) and index not in visited
        visited.add(index)
        node = nodes[index]
        assert node["state"] == expected
        kind = node["kind"]
        if kind == "FORCE":
            assert all(item["kind"] in ("EMPTY", "SPLIT", "DUAL") for item in node["force_nodes"])
            result = exact.verify(B, expected["next"], expected["faces"], node["force_nodes"], constants)
            assert result == node["exact_result"] and result["verified"]
            if result["minimum_force_margin"] is not None:
                margin = F(result["minimum_force_margin"])
                assert margin > 0
                minimum = margin if minimum is None else min(minimum, margin)
            else:
                assert result["counts"].get("EMPTY", 0) > 0
            force += 1
        elif kind == "ANGLE":
            assert verify_cycle(B, expected["next"], expected["faces"], node["cycle"], constants) == node["exact_cycle_check"]
            angles += 1
        else:
            following = children(expected, N, B)
            if kind == "SPLIT":
                assert following is not None and len(following) > 0
                assert len(node["children"]) == len(following)
                work.extend(zip(node["children"], following, strict=True))
                split += 1
            elif kind == "DEAD":
                assert following == []
                dead += 1
            elif kind == "FULL_PENDING":
                assert following is None
                pending_full += 1
            else:
                assert kind == "FRONTIER"
                frontier += 1
    assert visited == set(range(len(nodes)))
    return {"verified": True, "N": N, "B": B, "collar_centers": centers, "collar_faces": outer,
            "complete_same_simple_hole_family_branch_cover_checked": True,
            "exact_force_leaves": force, "exact_angle_leaves": angles,
            "split_nodes": split, "dead_nodes": dead, "nodes": len(nodes),
            "pending_complete_leaves": pending_full, "unsearched_frontier_nodes": frontier,
            "all_full_simple_disk_completions_strictly_paid": pending_full == frontier == 0,
            "minimum_force_margin": None if minimum is None else str(minimum),
            "not_a_standalone_geometric_weak_graph_exclusion": True,
            "not_a_complete_boundary_family": True}
