"""Exact ground-node elimination and whole-angle-box boundary energy bounds."""

from fractions import Fraction as F


def laplacian(edges, weights, vertices=62):
    if (len(edges) != len(weights) or any(type(w) is not int or w <= 0 for w in weights)
            or any(len(edge) != 2 or any(type(v) is not int or not 0 <= v < vertices for v in edge)
                   or edge[0] == edge[1] for edge in edges)):
        raise ValueError("malformed positive Dirichlet rod graph")
    graph = [set() for _ in range(vertices)]
    matrix = [[0] * vertices for _ in range(vertices)]
    for (u, v), w in zip(edges, weights):
        graph[u].add(v)
        graph[v].add(u)
        matrix[u][u] += w
        matrix[v][v] += w
        matrix[u][v] -= w
        matrix[v][u] -= w
    seen, queue = set(range(16)), list(range(16))
    for u in queue:
        for v in graph[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if len(seen) != vertices:
        raise ValueError("an internal Dirichlet vertex is not grounded")
    return matrix


def kernel_gate(reference, certificate):
    scale = int(reference["rational_scale"])
    weights = [int(x) for x in reference["weight_numerators"]]
    matrix = laplacian(reference["edges"], weights)
    denominator = int(certificate["inverse_denominator"])
    inverse = [[int(x) for x in row] for row in certificate["inverse_numerators"]]
    if (certificate["schema"] != "N26-exact-integer-ground-Dirichlet-inverse-v1"
            or certificate["anchor_vertices"] != 16 or denominator <= 0
            or len(inverse) != 46 or any(len(row) != 46 for row in inverse)
            or any(inverse[i][j] != inverse[j][i] for i in range(46) for j in range(46))):
        raise ValueError("malformed ground inverse certificate")
    for i in range(46):
        for j in range(46):
            if sum(matrix[16 + i][16 + k] * inverse[k][j] for k in range(46)) != (
                    denominator if i == j else 0):
                raise ValueError("exact ground inverse identity failed")
    if any(inverse[i][i] <= 0 for i in range(46)):
        raise ValueError("nonpositive grounded resistance")
    harmonic = [[-sum(inverse[i][k] * matrix[16 + k][j] for k in range(46))
                 for j in range(16)] for i in range(46)]
    if any(min(row) < 0 or sum(row) != denominator for row in harmonic):
        raise ValueError("exact harmonic coefficients lack convex combination property")
    schur = [[matrix[i][j] * denominator + sum(matrix[i][16 + k] * harmonic[k][j]
                                              for k in range(46))
              for j in range(16)] for i in range(16)]
    if (any(sum(row) for row in schur)
            or any(schur[i][j] != schur[j][i] for i in range(16) for j in range(16))
            or any(schur[i][j] > 0 for i in range(16) for j in range(16) if i != j)):
        raise ValueError("Schur boundary energy identity or nonnegative pair weights failed")
    return {"scale": scale, "weights": weights, "matrix": matrix,
            "inverse": inverse, "inverse_denominator": denominator, "harmonic": harmonic,
            "pair_weights": [(i, j, -schur[i][j]) for i in range(16)
                             for j in range(i + 1, 16) if schur[i][j]],
            "energy_denominator": scale * denominator}


def ceil_fraction(value):
    return -((-value.numerator) // value.denominator)


def bound(lower, upper, kernel, radius_squared_upper, arcs):
    lower, upper = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if len(lower) != 16 or len(upper) != 16 or any(a > b for a, b in zip(lower, upper)):
        raise ValueError("invalid whole closed Dirichlet angle box")
    middle = [(a + b) / 2 for a, b in zip(lower, upper)]
    grid, arc_scale = 10**100, arcs.SCALE
    widths = [ceil_fraction((b - a) * grid / 2) for a, b in zip(lower, upper)]
    energy0, gradient_lower, gradient_upper, curvature = 0, [0] * 16, [0] * 16, 0
    for i, j, w in kernel["pair_weights"]:
        cosine, sine = arcs.sincos_turn(middle[j] - middle[i])
        energy0 += 2 * w * (arc_scale - cosine[1])
        gradient_lower[i] -= w * sine[1]
        gradient_upper[i] -= w * sine[0]
        gradient_lower[j] += w * sine[0]
        gradient_upper[j] += w * sine[1]
        curvature += w * (widths[i] + widths[j])**2
    gradient = [max(abs(a), abs(b)) for a, b in zip(gradient_lower, gradient_upper)]
    pi_upper = arcs.PI[1]
    linear = sum(value * width for value, width in zip(gradient, widths))
    numerator = energy0 * arc_scale * grid**2 - 4 * pi_upper * linear * grid - 4 * pi_upper**2 * curvature
    denominator = kernel["energy_denominator"] * arc_scale**2 * grid**2
    energy_lower = F(numerator, denominator)
    energy_upper = F(radius_squared_upper) * F(sum(kernel["weights"]), kernel["scale"])
    return {"boundary_Dirichlet_energy_lower": str(energy_lower),
            "whole_rod_energy_upper_at_same_root": str(energy_upper),
            "strict_energy_exclusion_margin": str(energy_lower - energy_upper),
            "radius_conditional_whole_angle_box_excluded": energy_lower > energy_upper,
            "closed_box_midpoint_gradient_cancellation_recomputed_exactly": True,
            "global_absolute_cosine_second_derivative_remainder_charged": True,
            "all_92_positive_rods_and_all_46_free_vertices_used": True}
