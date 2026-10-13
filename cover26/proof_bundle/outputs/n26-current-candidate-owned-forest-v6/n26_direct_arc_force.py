"""Integer cycle flows with exact direct support bounds on whole circle arcs."""

from fractions import Fraction as F

from n26_force import ceilroot, load_trig, rod_graph, spanning_tree


def arc_dot_lower(g, lo, hi, arcs):
    lo, hi = F(lo), F(hi)
    if not 0 <= hi - lo < F(1, 2):
        raise ValueError("invalid direct-force angular interval")
    co, si = arcs.sincos_turn((lo + hi) / 2)
    gx, gy = g

    def scale(k, interval):
        return (k * interval[0], k * interval[1]) if k >= 0 else (k * interval[1], k * interval[0])

    def add(a, b):
        return a[0] + b[0], a[1] + b[1]

    value = add(scale(gx, co), scale(gy, si))
    derivative = add(scale(-gx, si), scale(gy, co))
    norm_upper = ceilroot(gx * gx + gy * gy)
    halfwidth_radians_upper = F(arcs.PI[1], arcs.SCALE) * (hi - lo)
    return (F(value[0], arcs.SCALE)
            - F(max(abs(derivative[0]), abs(derivative[1])), arcs.SCALE) * halfwidth_radians_upper
            - F(norm_upper, 2) * halfwidth_radians_upper**2)


def force_check(spec, lower, upper, cert, arcs=None):
    b = spec["B"]
    vertices, edges = rod_graph(spec)
    parent, order, chords = spanning_tree(vertices, edges)
    arcs = arcs or load_trig()[0]
    q, loads, cycles = cert["q"], cert["g"], cert["f"]
    if (type(q) is not int or not 0 < q <= 10**60
            or len(loads) != 2 * (b - 1) or len(cycles) != 2 * len(chords)
            or any(type(x) is not int or x.bit_length() > 800 for x in loads + cycles)
            or len(lower) != b - 1 or len(upper) != b - 1):
        raise ValueError("invalid direct-arc force coefficients")
    balance = [[0, 0] for _ in range(vertices)]
    for i in range(1, b):
        for d in range(2):
            balance[i][d] = loads[2 * (i - 1) + d]
            balance[0][d] -= balance[i][d]
    flow = [[0, 0] for _ in edges]
    for j, k in enumerate(chords):
        u, v = edges[k]
        for d in range(2):
            flow[k][d] = cycles[2 * j + d]
            balance[u][d] -= flow[k][d]
            balance[v][d] += flow[k][d]
    for v in reversed(order[1:]):
        u, k = parent[v]
        sign = 1 if edges[k][0] == v else -1
        for d in range(2):
            flow[k][d] = sign * balance[v][d]
            balance[u][d] += balance[v][d]
            balance[v][d] = 0
    if any(any(row) for row in balance):
        raise ValueError("direct-arc force reconstruction leaves a residual")
    actual = [[0, 0] for _ in range(vertices)]
    for (u, v), f in zip(edges, flow):
        for d in range(2):
            actual[u][d] += f[d]
            actual[v][d] -= f[d]
    for i in range(1, vertices):
        expected = loads[2 * (i - 1):2 * i] if i < b else [0, 0]
        if actual[i] != expected:
            raise ValueError("fresh direct-arc divergence check failed")
    if actual[0] != [-sum(actual[i][d] for i in range(1, vertices)) for d in range(2)]:
        raise ValueError("root direct-arc divergence check failed")
    denominator = sum(ceilroot(x * x + y * y) for x, y in flow)
    if denominator <= 0:
        raise ValueError("zero direct-arc force")
    numerator = sum(
        (arc_dot_lower(loads[2 * i:2 * i + 2], lo, hi, arcs) - loads[2 * i]
         for i, (lo, hi) in enumerate(zip(lower, upper))), F(0))
    required_radius_lower = numerator / denominator
    return {
        "required_radius_lower": str(required_radius_lower),
        "vertices": vertices, "edges": len(edges), "cycle_edges": len(chords),
        "direct_exact_unit_circle_arc_support_used": True,
        "integer_divergence_recomputed_exactly": True,
    }


def regular_ring_controls(arcs):
    spec = {"N": 26, "B": 14, "next": 14, "faces": []}
    b = spec["B"]
    vertices, edges = rod_graph(spec)
    chords = spanning_tree(vertices, edges)[2]
    angles = [F(i, b) for i in range(1, b)]
    radius_iv = arcs.sincos_turn(F(1, 2 * b))[1]
    radius_lower, radius_upper = [F(x, arcs.SCALE) for x in radius_iv]
    for seed in range(32):
        cert = {
            "q": 1000, "g": [((seed + 5 * i) % 11) - 5 for i in range(2 * (b - 1))],
            "f": [((seed + 7 * i) % 23) - 11 for i in range(2 * len(chords))],
        }
        result = force_check(spec, angles, angles, cert, arcs)
        if F(result["required_radius_lower"]) > radius_upper:
            raise AssertionError("known feasible regular ring falsely excluded by direct arc force")
    q = 10**30

    def nearest(x):
        return (2 * x.numerator + x.denominator) // (2 * x.denominator)

    points = [[nearest(F(a + c, 2 * arcs.SCALE) * q) for a, c in arcs.sincos_turn(F(i, b))]
              for i in range(b)]
    flow = [[points[i][d] - points[(i - 1) % b][d] for d in range(2)] for i in range(b)]
    flow += [[points[i][d] - points[(i + 1) % b][d] for d in range(2)] for i in range(b)]
    loads = [[flow[i][d] + flow[b + i][d] for d in range(2)] for i in range(1, b)]
    cert = {"q": q, "g": [x for row in loads for x in row],
            "f": [flow[k][d] for k in chords for d in range(2)]}
    value = F(force_check(spec, angles, angles, cert, arcs)["required_radius_lower"])
    if not radius_lower - F(1, 10**20) < value <= radius_upper:
        raise AssertionError("direct arc force does not tightly recover exact regular-ring radius")
    return {"random_feasible_ring_controls": 32,
            "near_equality_ring_force_control": True,
            "near_equality_absolute_gap_upper": "1/100000000000000000000"}
