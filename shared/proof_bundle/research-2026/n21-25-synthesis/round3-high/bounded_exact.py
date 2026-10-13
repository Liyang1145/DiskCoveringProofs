"""New exact force format: support vectors at every bounded nonfixed node.

BDUAL is intentionally distinct from old DUAL.  Its b vector has 2*(V-1)
entries, and all nonanchor divergence is reconstructed, not assumed zero.
"""
from fractions import Fraction as F
from collections import Counter
import exact_graph as exact
from actual_norm_bounds import constants as norm_constants

if not __debug__:
    raise RuntimeError("Assertions must be enabled")
K = exact.kernel


def force_margin(B, V, edges, lo, hi, certificate, U, radii):
    assert set(certificate) == {"q", "l", "b", "f"}
    Q, la, beta, cycles = (certificate[key] for key in ("q", "l", "b", "f"))
    assert type(Q) is int and 0 < Q <= 10**18
    assert len(la) == B-1 and all(type(v) is int and v >= 0 for v in la)
    assert len(beta) == 2*(V-1) and all(type(v) is int for v in beta+cycles)
    assert len(radii) == V-1 and all(F(v) >= 0 for v in radii)
    assert K.QB % K.QA == 0
    parent, order, chords = K.tree(V, tuple(edges))
    assert len(cycles) == 2*len(chords)
    aa, bb = [], []
    for lower, upper in zip(lo, hi):
        a, b = K.arc_halfplane(lower, upper)
        aa.append(a)
        bb.append(b)
    target = [[0, 0] for _ in range(V)]
    for node in range(1, V):
        for axis in (0, 1):
            target[node][axis] -= beta[2*(node-1)+axis]*K.QA
    for i in range(B-1):
        for axis in (0, 1):
            target[i+1][axis] += la[i]*aa[i][axis]
    for axis in (0, 1):
        target[0][axis] = -sum(row[axis] for row in target[1:])
    balance = [list(row) for row in target]
    flow = [[0, 0] for _ in edges]
    for j, edge in enumerate(chords):
        u, v = edges[edge]
        for axis in (0, 1):
            value = cycles[2*j+axis]*K.QA
            flow[edge][axis] = value
            balance[u][axis] -= value
            balance[v][axis] += value
    for node in reversed(order[1:]):
        ancestor, edge = parent[node]
        sign = 1 if edges[edge][0] == node else -1
        for axis in (0, 1):
            flow[edge][axis] = sign*balance[node][axis]
            balance[ancestor][axis] += balance[node][axis]
            balance[node][axis] = 0
    assert all(row == [0, 0] for row in balance)
    divergence = [[0, 0] for _ in range(V)]
    for (u, v), vector in zip(edges, flow):
        for axis in (0, 1):
            divergence[u][axis] += vector[axis]
            divergence[v][axis] -= vector[axis]
    assert divergence == target
    normsum = sum(K.ceil_root(x*x+y*y) for x, y in flow)
    assert normsum > 0
    ratio = K.QB//K.QA
    work = F(sum(la[i]*(bb[i]-aa[i][0]*ratio) for i in range(B-1)))
    for i, radius in enumerate(radii):
        x, y = beta[2*i:2*i+2]
        norm = K.ceil_root((x*K.QA)**2+(y*K.QA)**2)
        work += (x*K.QA-F(radius)*norm)*ratio
    return work*K.QA/(K.QB*normsum)-U


def verify(actualN, B, centers, masks, nodes):
    base, radii, premise = norm_constants(actualN, B, centers, len(masks))
    faces, edges, V = exact.graph(B, centers, masks)
    matrix = K.angle_bounds(B, centers, faces, base)
    D, U = base["angle_scale"], F(base["radius_upper"])
    lo, hi = exact.rootbox(matrix, D)
    pending = [(0, lo, hi)]
    seen, counts = set(), Counter()
    minimum = None
    while pending:
        index, lo, hi = pending.pop()
        assert type(index) is int and 0 <= index < len(nodes) and index not in seen
        seen.add(index)
        node = nodes[index]
        assert node["kind"] in ("EMPTY", "SPLIT", "BDUAL", "DUAL")
        box = K.tighten(matrix, lo, hi, D)
        if node["kind"] == "EMPTY":
            assert box is None
        else:
            assert box is not None
            lo, hi = box
            if node["kind"] in ("BDUAL", "DUAL"):
                if node["kind"] == "BDUAL":
                    margin = force_margin(B, V, edges, lo, hi, node["certificate"], U, radii)
                else:
                    margin = K.force_margin(B, V, edges, lo, hi, node["certificate"], U)
                assert margin > 0
                minimum = margin if minimum is None else min(minimum, margin)
            else:
                axis, cut, children = node["axis"], F(node["mid"]), node["children"]
                assert type(axis) is int and 0 <= axis < B-1 and lo[axis] < cut < hi[axis]
                assert len(children) == 2 and children[0] != children[1]
                assert all(type(j) is int and 0 <= j < len(nodes) for j in children)
                left, right = list(hi), list(lo)
                left[axis], right[axis] = cut, cut
                pending.extend([(children[0], list(lo), left), (children[1], right, list(hi))])
        counts[node["kind"]] += 1
    assert seen == set(range(len(nodes))) and minimum is not None
    return {"verified": True, "nodes": len(nodes), "counts": dict(counts),
            "minimum_force_margin": str(minimum), "norm_premise": premise,
            "scope": "actual-cover necessary bounded realization at U on whole angle domain",
            "unrestricted_auxiliary_graph_exclusion_claimed": False}
