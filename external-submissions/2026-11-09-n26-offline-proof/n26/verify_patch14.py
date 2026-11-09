"""Check rational vector-flow cuts for consecutive pieces of a b=14 belt."""

import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

from rational_trig import cos_lower, cos_upper, pi_bounds, sin_lower, sin_upper, sqrt_bounds
from verify_belt14 import ARC_CAP, RADIUS
from verify_fan import require


def patch_graph(blocks, extras):
    """Return number of free nodes, number of arcs and directed edges."""
    require(len(blocks) >= 2 and all(x in (1, 2) for x in blocks), "Invalid blocks")
    require(len(extras) == len(blocks) - 1 and all(
        isinstance(x, int) and 0 <= x <= 9 for x in extras
    ), "Invalid link lengths")
    arcs = 1 + sum(blocks)
    require(arcs <= 14, "The patch wraps past its first arc")
    site_count = arcs + len(blocks)
    faces = []
    i = 0
    for j, width in enumerate(blocks):
        apex = arcs + j
        if j:
            path = [apex - 1, *range(site_count, site_count + extras[j - 1]), apex]
            site_count += extras[j - 1]
            faces.extend((i, u, v) for u, v in zip(path, path[1:]))
        faces.extend((k, k + 1, apex) for k in range(i, i + width))
        i += width
    free = site_count + len(faces)
    edges = [(u, site_count + j) for j, face in enumerate(faces) for u in face]
    edges.extend((i, free + i + j) for i in range(arcs) for j in range(2))
    return free, arcs, edges


@lru_cache(maxsize=8192)
def trig_bounds(angle):
    a = abs(angle)
    require(a < 4, "Taylor range")
    s0, s1 = sin_lower(a), sin_upper(a)
    if angle < 0:
        s0, s1 = -s1, -s0
    return cos_lower(a), cos_upper(a), s0, s1


def trig_dot_lower(vec, angle):
    x, y = vec
    c0, c1, s0, s1 = trig_bounds(angle)
    return x * (c0 if x >= 0 else c1) + y * (s0 if y >= 0 else s1)


def terminals(flows, free, arcs, edges, last_ratio=Q(1)):
    require(len(edges) == len(flows), "Wrong number of flow vectors")
    balance = [[0, 0] for _ in range(free + arcs + 1)]
    cost = Q(0)
    for i, ((u, v), flow) in enumerate(zip(edges, flows)):
        require(len(flow) == 2 and all(type(x) is int for x in flow),
                "Use two integer coordinates per flow")
        x, y = flow
        balance[u][0] -= x
        balance[u][1] -= y
        balance[v][0] += x
        balance[v][1] += y
        if x or y:
            _, hi = sqrt_bounds(Q(x * x + y * y))
            cost += hi * (last_ratio if i == len(edges) - 1 else 1)
    require(cost > 0 and not any(x or y for x, y in balance[:free]),
            "The flow is zero or does not balance at a free node")
    return balance[free:], cost


def axes(n, value):
    return [[value if i == j else Q(0) for j in range(n)] for i in range(n)]


def angle_vertices(weights, weighted_deficits):
    """Map weighted deficit vertices to angles, centering the two end seams."""
    for row in weighted_deficits:
        gaps = [ARC_CAP - value / w for value, w in zip(row, weights)]
        a = -sum(gaps) / 2
        vertices = [a]
        for gap in gaps:
            a += gap
            vertices.append(a)
        yield vertices


def flow_row(end, cost, vertices):
    values = [sum(trig_dot_lower(v, a) for v, a in zip(end, row)) for row in vertices]
    error = Q(0)
    for v, angles in zip(end, zip(*vertices)):
        lo, hi = min(angles), max(angles)
        mid = (lo + hi) / 2
        smallest = trig_dot_lower(v, mid) - (abs(v[0]) + abs(v[1])) * (hi - lo) / 2
        # F'' = -F. A nonzero upper bound on F'' costs at most the
        # corresponding Jensen variance correction over this interval.
        error += max(Q(0), -smallest) * (hi - lo)**2 / 8
    return [value - error - RADIUS * cost for value in values]


def flow_margin(end, cost, vertices):
    return min(flow_row(end, cost, vertices))


def cut_margin(entry):
    """Return a rigorous lower bound on min of the flow surplus over the simplex."""
    require(sin_lower(ARC_CAP / 2) > RADIUS, "Arc upper bound failed")
    blocks = entry["blocks"]
    extras = entry.get("extras", [0] * (len(blocks) - 1))
    free, arcs, edges = patch_graph(blocks, extras)
    weights = [Q(w) for w in entry.get("weights", [1] * arcs)]
    deficit = Q(entry["deficit"])
    require(len(weights) == arcs and all(w > 0 for w in weights), "Invalid weights")
    require(0 <= deficit <= ARC_CAP * min(weights), "Deficit domain too large")

    def margin(flow, vertices):
        end, cost = terminals(flow, free, arcs, edges)
        return flow_margin(end, cost, list(angle_vertices(weights, vertices)))

    zero = [Q(0)] * arcs
    if "mixture" in entry:
        vertices = list(angle_vertices(weights, [zero, *axes(arcs, deficit)]))
        row = [Q(0)] * len(vertices)
        for weight, flow in entry["mixture"]:
            w = Q(weight)
            require(w > 0, "Mixture weights must be positive")
            end, cost = terminals(flow, free, arcs, edges)
            row = [a + w * b for a, b in zip(row, flow_row(end, cost, vertices))]
        return min(row)
    if "threshold" not in entry:
        return margin(entry["flow"], [zero, *axes(arcs, deficit)])

    threshold = Q(entry["threshold"])
    require(deficit / 2 < threshold < deficit, "Invalid corner threshold")
    flows = entry["corners"]
    require(len(flows) == arcs, "Wrong number of corner flows")
    # No two coordinates can exceed threshold. A vertex of the truncated
    # simplex has either one capped coordinate or one cap and the sum tight.
    cap_vertices = axes(arcs, threshold)
    corner_axes = axes(arcs, deficit - threshold)
    cap_vertices.extend(
        [a + b for a, b in zip(x, y)]
        for i, x in enumerate(cap_vertices[:arcs])
        for j, y in enumerate(corner_axes) if i != j
    )
    result = margin(entry["flow"], [zero, *cap_vertices])
    for x, flow in zip(axes(arcs, threshold), flows):
        result = min(result, margin(flow, [x, *(
            [a + b for a, b in zip(x, y)] for y in corner_axes
        )]))
    return result


def total_deficit_upper():
    pi0, _ = pi_bounds()
    return 14 * ARC_CAP - 2 * pi0


def verify(entries):
    for entry in entries:
        margin = cut_margin(entry)
        require(margin > 0, f"Unverified cut for {entry['blocks']}")
        print(f"PASS b=14 patch {entry['blocks']}, "
              f"extras={entry.get('extras', [])}, deficit > {entry['deficit']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    entries = json.loads(args.certificate.read_text(encoding="utf-8"))
    require(bool(entries), "Empty certificate")
    verify(entries)


if __name__ == "__main__":
    main()
