"""Circle-arc Taylor support with exact nonnegative difference duals."""

from fractions import Fraction as F

import n26_direct_arc_force as direct
from n26_force import ceilroot, rod_graph, spanning_tree
from n26_sharp_radius_constraints import SCALE


def scale_interval(k, interval):
    return (k * interval[0], k * interval[1]) if k >= 0 else (k * interval[1], k * interval[0])


def midpoint_data(g, lo, hi, arcs):
    co, si = arcs.sincos_turn((lo + hi) / 2)
    x, y = scale_interval(g[0], co), scale_interval(g[1], si)
    value = F(x[0] + y[0], arcs.SCALE)
    x, y = scale_interval(-g[0], si), scale_interval(g[1], co)
    tangent = (F(x[0] + y[0], arcs.SCALE), F(x[1] + y[1], arcs.SCALE))
    products = [2 * F(p, arcs.SCALE) * d for p in arcs.PI for d in tangent]
    return value, (min(products), max(products))


def flow_denominator(spec, cert):
    vertices, edges = rod_graph(spec)
    parent, order, chords = spanning_tree(vertices, edges)
    balance = [[0, 0] for _ in range(vertices)]
    for i in range(1, spec["B"]):
        for d in range(2):
            balance[i][d] = cert["g"][2 * (i - 1) + d]
            balance[0][d] -= balance[i][d]
    flow = [[0, 0] for _ in edges]
    for j, k in enumerate(chords):
        u, v = edges[k]
        for d in range(2):
            flow[k][d] = cert["f"][2 * j + d]
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
        raise ValueError("correlated-force tree reconstruction has residual")
    actual = [[0, 0] for _ in range(vertices)]
    for (u, v), row in zip(edges, flow):
        for d in range(2):
            actual[u][d] += row[d]
            actual[v][d] -= row[d]
    for i in range(1, vertices):
        expected = cert["g"][2 * (i - 1):2 * i] if i < spec["B"] else [0, 0]
        if actual[i] != expected:
            raise ValueError("correlated-force fresh divergence mismatch")
    if actual[0] != [-sum(actual[i][d] for i in range(1, vertices)) for d in range(2)]:
        raise ValueError("correlated-force root divergence mismatch")
    return sum(ceilroot(x * x + y * y) for x, y in flow)


def force_check(spec, lower, upper, matrix, cert, arcs):
    if set(cert) != {"q", "g", "f", "mu"}:
        raise ValueError("correlated-force certificate has unverified fields")
    base = {key: cert[key] for key in ("q", "g", "f")}
    baseline = direct.force_check(spec, lower, upper, base, arcs)
    b = spec["B"]
    if (len(matrix) != b or any(len(row) != b for row in matrix)
            or any(type(n) is not int for row in matrix for n in row)):
        raise ValueError("invalid certified angle-difference matrix")
    lo, hi = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    midpoint = [(a + c) / 2 for a, c in zip(lo, hi)]
    divergence, cost, seen = [F(0)] * b, F(0), set()
    if type(cert["mu"]) is not list or len(cert["mu"]) > b * (b - 1):
        raise ValueError("invalid difference-dual list")
    for row in cert["mu"]:
        if type(row) is not list or len(row) != 3:
            raise ValueError("malformed difference-dual coefficient")
        i, j, text = row
        if (type(i) is not int or type(j) is not int or not 0 <= i < b
                or not 0 <= j < b or i == j or (i, j) in seen
                or not isinstance(text, (str, int))):
            raise ValueError("invalid or repeated difference-dual edge")
        mu = F(text)
        if mu < 0 or max(mu.numerator.bit_length(), mu.denominator.bit_length()) > 800:
            raise ValueError("difference dual must be nonnegative and finite")
        seen.add((i, j))
        bound = min(F(matrix[i][j], SCALE), hi[j] - lo[i])
        divergence[i] += mu
        divergence[j] -= mu
        cost += mu * bound
    if sum(divergence) != 0:
        raise ValueError("difference-dual divergence is not exactly balanced")
    numerator, errors = -cost, []
    for i in range(1, b):
        g = cert["g"][2 * (i - 1):2 * i]
        value, derivative = midpoint_data(g, lo[i], hi[i], arcs)
        error = max(abs(a - divergence[i]) for a in derivative)
        halfwidth = (hi[i] - lo[i]) / 2
        radian_halfwidth = F(arcs.PI[1], arcs.SCALE) * (hi[i] - lo[i])
        curvature = F(ceilroot(g[0]**2 + g[1]**2), 2) * radian_halfwidth**2
        numerator += value - divergence[i] * midpoint[i] - error * halfwidth - curvature - g[0]
        errors.append(str(error))
    denominator = flow_denominator(spec, base)
    if denominator <= 0:
        raise ValueError("zero correlated force")
    bound = numerator / denominator
    if not cert["mu"] and bound != F(baseline["required_radius_lower"]):
        raise ValueError("zero dual failed to reduce exactly to direct-arc support")
    return {
        "required_radius_lower": str(bound),
        "direct_arc_required_radius_lower": baseline["required_radius_lower"],
        "vertices": baseline["vertices"], "edges": baseline["edges"],
        "cycle_edges": baseline["cycle_edges"],
        "difference_dual_terms": len(cert["mu"]),
        "difference_dual_nonnegativity_checked": True,
        "difference_dual_divergence_recomputed_exactly": list(map(str, divergence)),
        "turn_derivative_full_interval_errors_charged": errors,
        "integer_force_divergence_recomputed_exactly": True,
        "whole_closed_circle_arc_curvature_remainder_charged": True,
    }


def controls(arcs):
    result = direct.regular_ring_controls(arcs)
    spec = {"N": 26, "B": 14, "next": 14, "faces": []}
    b = spec["B"]
    angles = [F(i, b) for i in range(1, b)]
    matrix = [[0 if i == j else SCALE for j in range(b)] for i in range(b)]
    chords = spanning_tree(*rod_graph(spec))[2]
    for seed in range(32):
        base = {"q": 1000,
                "g": [((seed + 5 * i) % 11) - 5 for i in range(2 * (b - 1))],
                "f": [((seed + 7 * i) % 23) - 11 for i in range(2 * len(chords))]}
        mu = [[i, (i + 1) % b, str(F(seed + i + 1, 7))] for i in range(b)]
        actual = force_check(spec, angles, angles, matrix, {**base, "mu": mu}, arcs)
        expected = direct.force_check(spec, angles, angles, base, arcs)
        if actual["required_radius_lower"] != expected["required_radius_lower"]:
            raise AssertionError("fixed-angle nonzero dual changed direct-force value")
        lo, hi = [a - F(1, 100000) for a in angles], [a + F(1, 100000) for a in angles]
        actual = force_check(spec, lo, hi, matrix, {**base, "mu": mu}, arcs)
        fixed = F(expected["required_radius_lower"])
        if F(actual["required_radius_lower"]) > fixed:
            raise AssertionError("whole-box correlated support exceeds an included fixed-angle support")
        force_check(spec, lo, hi, matrix, {**base, "mu": []}, arcs)
    return {**result, "fixed_angle_nonzero_dual_exact_reductions": 32,
            "whole_box_included_ring_support_controls": 32,
            "zero_dual_whole_box_exact_reductions": 32}
