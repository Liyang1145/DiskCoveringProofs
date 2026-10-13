"""General n<=25 graph/tree checker using the frozen n21 integer force kernel.

No solver or mutable geometry globals are used by the accepting path.
Local leaves require an explicit exact per-instance callback.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round2-grouped"))
import partial_force_exact as kernel
assert __debug__


def graph(B, N, masks):
    assert type(B) is int and type(N) is int and 3 <= B <= N <= 25
    assert masks == sorted(set(masks))
    assert all(type(m) is int and m > 0 and m < (1 << N) and m.bit_count() == 3 for m in masks)
    faces = [kernel.bits(m) for m in masks]
    edges = ([(i, B+i) for i in range(B)] +
             [(i, B+(i+1) % B) for i in range(B)] +
             [(B+N+k, B+j) for k, face in enumerate(faces) for j in face])
    V = B+N+len(faces)
    assert sorted({v for edge in edges for v in edge}) == list(range(V))
    return faces, edges, V


def rootbox(mat, D):
    return ([F(-mat[i][0], D) for i in range(1, len(mat))],
            [F(mat[0][i], D) for i in range(1, len(mat))])


def verify(B, N, masks, nodes, constants, local=None):
    faces, edges, V = graph(B, N, masks)
    mat = kernel.angle_bounds(B, N, faces, constants)
    D = constants["angle_scale"]
    U = F(constants["radius_upper"])
    lo, hi = rootbox(mat, D)
    pending = [(0, lo, hi)]
    seen = set()
    counts = Counter()
    force_min = local_min = None
    while pending:
        index, lo, hi = pending.pop()
        assert type(index) is int and 0 <= index < len(nodes) and index not in seen
        seen.add(index)
        node = nodes[index]
        assert isinstance(node, dict) and node["kind"] in ("EMPTY", "SPLIT", "DUAL", "LOCAL")
        box = kernel.tighten(mat, lo, hi, D)
        if node["kind"] == "EMPTY":
            assert box is None
        else:
            assert box is not None
            lo, hi = box
            if node["kind"] == "DUAL":
                margin = kernel.force_margin(B, V, edges, lo, hi, node["certificate"], U)
                assert margin > 0
                force_min = margin if force_min is None else min(force_min, margin)
            elif node["kind"] == "LOCAL":
                assert local is not None
                margin = local(lo, hi)
                assert margin is not None and margin > 0
                local_min = margin if local_min is None else min(local_min, margin)
            else:
                axis, cut, children = node["axis"], F(node["mid"]), node["children"]
                assert type(axis) is int and 0 <= axis < B-1 and lo[axis] < cut < hi[axis]
                assert len(children) == 2 and children[0] != children[1]
                assert all(type(j) is int and 0 <= j < len(nodes) for j in children)
                left, right = list(hi), list(lo)
                left[axis], right[axis] = cut, cut
                pending.extend([(children[0], list(lo), left), (children[1], right, list(hi))])
        counts[node["kind"]] += 1
    assert seen == set(range(len(nodes)))
    return {"verified": True, "vertices": V, "edges": len(edges), "nodes": len(nodes),
            "counts": dict(counts),
            "minimum_force_margin": None if force_min is None else str(force_min),
            "minimum_local_margin": None if local_min is None else str(local_min)}
