"""Exact root-radius chord constraints, independently reconstructed.

Discovery uses breadth-first center paths and Floyd anchor closure. Acceptance
uses all-pairs center distances and Bellman--Ford difference-constraint paths.
"""

from fractions import Fraction as F

from n26_force import spec_gate


SCALE = 10**40


def cap_gate(radius_upper, certificate, arcs):
    radius_upper = F(radius_upper)
    if (certificate["N"] != 26 or certificate["radius_scope"] != "same-root-Rstar"
            or F(certificate["radius_upper"]) != radius_upper
            or int(certificate["scale"]) != SCALE or not 0 < radius_upper < F(1, 4)):
        raise ValueError("sharp caps not bound to the certified N26 radius")
    caps = tuple(int(n) for n in certificate["caps"])
    if len(caps) != 4 or not 0 < caps[0] < caps[1] < caps[2] < caps[3] < SCALE // 2:
        raise ValueError("invalid outward sharp-angle caps")
    margins = [F(arcs.sincos_turn(F(cap, 2 * SCALE))[1][0], arcs.SCALE) - k * radius_upper
               for k, cap in enumerate(caps, 1)]
    if min(margins) <= 0:
        raise ValueError("sharp chord cap has no strict certified sine margin")
    return caps, margins


def constraint_matrix(spec, caps, scale=SCALE):
    b, n, faces, adjacency = spec_gate(spec)
    if scale != SCALE or len(caps) != 4:
        raise ValueError("wrong sharp constraint constants")
    infinity = n + 1
    distance = [[0 if i == j else 1 if adjacency[i] >> j & 1 else infinity
                 for j in range(n)] for i in range(n)]
    for w in range(n):
        for u in range(n):
            for v in range(n):
                distance[u][v] = min(distance[u][v], distance[u][w] + distance[w][v])
    bounds = {}

    def edge(u, v, value):
        bounds[u, v] = min(bounds.get((u, v), 2 * scale), value)

    for i in range(b):
        j = (i + 1) % b
        edge(i, j, caps[0] - (scale if j == 0 else 0))
        edge(j, i, scale if j == 0 else 0)
    witnesses = []
    for i in range(b):
        for j in range(i + 1, b):
            h = min(distance[u][v] for u in (i, (i + 1) % b) for v in (j, (j + 1) % b))
            if h > 3:
                continue
            cap, steps = caps[h], j - i
            if min(steps, b - steps) * caps[0] <= cap:
                continue
            forward = steps * caps[0] < scale - cap
            backward = (b - steps) * caps[0] < scale - cap
            witnesses.append({"anchors": [i, j], "center_path_edges": h,
                              "forward_forced_short": forward, "backward_forced_short": backward})
            if forward and backward:
                return None, {"reason": "both-complementary-arcs-forced-short", "witness": witnesses[-1]}
            if forward:
                edge(i, j, cap)
            if backward:
                edge(j, i, cap - scale)
    edges = [(u, v, value) for (u, v), value in sorted(bounds.items())]
    matrix = []
    for source in range(b):
        values = [None] * b
        values[source] = 0
        for _ in range(b - 1):
            changed = False
            for u, v, value in edges:
                if values[u] is None:
                    continue
                proposed = values[u] + value
                if values[v] is None or proposed < values[v]:
                    values[v], changed = proposed, True
            if not changed:
                break
        for u, v, value in edges:
            if values[u] is not None and values[v] is not None and values[v] > values[u] + value:
                return None, {"reason": "negative-difference-cycle", "source": source}
        if any(value is None for value in values):
            raise ValueError("sharp boundary difference graph disconnected")
        matrix.append(values)
    return matrix, {"direct_difference_edges": [list(row) for row in edges],
                    "forced_arc_path_witnesses": witnesses,
                    "center_distances_reconstructed_by_all_pairs_paths": True,
                    "anchor_closure_reconstructed_by_Bellman_Ford": True}


def tighten(matrix, lower, upper, scale=SCALE):
    if scale != SCALE:
        raise ValueError("wrong sharp contraction scale")
    b = len(matrix)
    lo, hi = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if len(lo) != b or len(hi) != b or any(a > c for a, c in zip(lo, hi)):
        raise ValueError("invalid sharp-radius leaf box")
    low = []
    high = []
    for target in range(b):
        low.append(max(lo[origin] - F(matrix[target][origin], scale) for origin in range(b)))
        high.append(min(hi[origin] + F(matrix[origin][target], scale) for origin in range(b)))
    if any(a > c for a, c in zip(low, high)):
        return None
    if low[0] != 0 or high[0] != 0:
        raise ValueError("sharp contraction failed to retain the fixed rotation gauge")
    return low[1:], high[1:]
