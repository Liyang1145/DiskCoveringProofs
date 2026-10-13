"""Own-order branch coverage: generic topology, exact N23/N24 force/cycle gates."""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from complete_simple_collar import simple_holes, bits
from general_collar_filling import children as unfiltered_children
from general_collar_filling_linked import internal_links_possible
from small_order_origin_caps import parameters
from eight_rod_angles import inequalities, verify_cycle
from angle_obstructions import find_cycle
from group_catalog import canonical_full
import exact_graph as exact

assert __debug__


@lru_cache(maxsize=2)
def own_parameters(N):
    assert type(N) is int and N in (23, 24)
    return parameters(N)


def constants_gate(constants, N, B):
    expected, cap8, _ = own_parameters(N)
    assert constants == expected
    assert [B, N-B] in constants["families"]
    assert 0 < F(constants["radius_upper"]) < F(1, 4)
    return cap8


def start_states(N, B, centers, outer):
    # Topology is order-neutral; small complete native controls may use N<23.
    # Mathematical accepting/proposing entry points separately require own N.
    assert all(type(v) is int for v in (N, B, centers))
    assert 3 <= B <= centers <= N <= 25
    assert outer and outer == sorted(set(outer))
    assert all(type(mask) is int and 0 < mask < 1 << centers
               and mask.bit_count() == 3 and mask & ((1 << B)-1) for mask in outer)
    try:
        simple_holes(centers, B, outer)
    except AssertionError as error:
        assert str(error) == "pinched hole boundary", "outside accepted complete outer collar domain"
    used = 0
    for mask in outer:
        used |= mask
    assert used == (1 << centers)-1
    assert len(outer) <= 2*N-B-2
    return [{"faces": list(outer), "next": centers, "pending": []}]


def children(state, N, B):
    # This unchanged imported function is fully N-parametric; its N25-only
    # start_states entry is neither called nor weakened.
    following = unfiltered_children(state, N, B)
    if following is None:
        return None
    answer, old = [], set(state["faces"])
    for child in following:
        added = set(child["faces"])-old
        assert len(added) == 1
        affected = bits(next(iter(added)))
        assert all(v >= B for v in affected)
        if internal_links_possible(child["faces"], affected):
            answer.append(child)
    return answer


def all_complete_codes(N, B, centers, outer, linked=True):
    stack, codes, calls = start_states(N, B, centers, outer), set(), 0
    while stack:
        state = stack.pop()
        calls += 1
        following = (children if linked else unfiltered_children)(state, N, B)
        if following is None:
            codes.add(canonical_full(N, B, state["faces"]))
        else:
            stack.extend(following)
    return codes, calls


def angle_exclusion(B, centers, faces, constants, cap8):
    cycle = find_cycle(B, inequalities(B, centers, faces, constants, cap8))
    if cycle is None:
        return None
    return {"kind": "ANGLE", "cycle": cycle,
            "exact_cycle_check": verify_cycle(B, centers, faces, cycle, constants, cap8)}


def replay_payload(payload, constants):
    assert payload["schema"] == "small-order-own-constant-complete-collar-branch-tree-v1"
    N, B, centers, outer = (
        payload[key] for key in ("N", "B", "collar_centers", "collar_faces"))
    cap8 = constants_gate(constants, N, B)
    assert payload["radius_upper"] == constants["radius_upper"] and payload["cap8"] == cap8
    roots, nodes = start_states(N, B, centers, outer), payload["nodes"]
    assert len(payload["roots"]) == len(roots)
    work = list(zip(payload["roots"], roots, strict=True))
    visited = set()
    force = angles = pending = frontier = split = dead = 0
    minimum = None
    while work:
        index, expected = work.pop()
        assert type(index) is int and 0 <= index < len(nodes) and index not in visited
        visited.add(index)
        node = nodes[index]
        assert node["state"] == expected
        kind = node["kind"]
        if kind == "FORCE":
            assert node["force_nodes"]
            assert all(item["kind"] in ("EMPTY", "SPLIT", "DUAL") for item in node["force_nodes"])
            result = exact.verify(B, expected["next"], expected["faces"], node["force_nodes"], constants)
            assert result == node["exact_result"] and result["verified"]
            if result["minimum_force_margin"] is None:
                assert result["counts"].get("EMPTY", 0) > 0
            else:
                margin = F(result["minimum_force_margin"])
                assert margin > 0
                minimum = margin if minimum is None else min(minimum, margin)
            force += 1
        elif kind == "ANGLE":
            assert verify_cycle(B, expected["next"], expected["faces"],
                                node["cycle"], constants, cap8) == node["exact_cycle_check"]
            angles += 1
        else:
            following = children(expected, N, B)
            if kind == "SPLIT":
                assert following and len(node["children"]) == len(following)
                work.extend(zip(node["children"], following, strict=True))
                split += 1
            elif kind == "DEAD":
                assert following == []
                dead += 1
            elif kind == "FULL_PENDING":
                assert following is None
                pending += 1
            else:
                assert kind == "FRONTIER"
                frontier += 1
    assert visited == set(range(len(nodes)))
    return {
        "verified": True, "N": N, "B": B, "collar_centers": centers, "collar_faces": outer,
        "all_own_order_completion_branches_reconstructed": True,
        "all_positive_force_and_own_eight_rod_cycles_freshly_math_replayed": True,
        "exact_force_leaves": force, "exact_angle_leaves": angles, "split_nodes": split,
        "dead_nodes": dead, "nodes": len(nodes), "pending_complete_leaves": pending,
        "unsearched_frontier_nodes": frontier,
        "whole_completion_family_strictly_closed": pending == frontier == 0,
        "minimum_force_margin": None if minimum is None else str(minimum),
        "not_a_standalone_geometric_weak_graph_exclusion": True,
        "not_a_complete_boundary_family": True, "global_optimality_proved": False,
    }
