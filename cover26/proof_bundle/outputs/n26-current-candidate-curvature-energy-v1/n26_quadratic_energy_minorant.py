"""Exact full-type quadratic energy with a proved negative-curvature allowance."""

from fractions import Fraction as F
from math import isqrt

from n26_force import rod_graph
from n26_sharp_radius_constraints import SCALE


ROUND_GRID = 10**40


def kernel_gate(spec, certificate):
    b = spec["B"]
    vertices, edges = rod_graph(spec)
    if spec["next"] != 26:
        raise ValueError("quadratic full-type proof applied to a partial complex")
    scale = certificate["weight_scale"]
    weights = certificate["weight_numerators"]
    den = int(certificate["inverse_denominator"])
    inverse = [[int(x) for x in row] for row in certificate["inverse_numerators"]]
    n = vertices - b
    if (certificate["schema"] != "N26-full-type-positive-quadratic-ground-kernel-v1"
            or certificate["spec"] != spec or type(scale) is not int or not 0 < scale <= 10**60
            or len(weights) != len(edges)
            or any(type(w) is not int or w <= 0 or w.bit_length() > 800 for w in weights)
            or den <= 0 or len(inverse) != n or any(len(row) != n for row in inverse)):
        raise ValueError("invalid full-type positive energy kernel")
    matrix = [[0] * vertices for _ in range(vertices)]
    graph = [set() for _ in range(vertices)]
    for (u, v), w in zip(edges, weights):
        matrix[u][u] += w
        matrix[v][v] += w
        matrix[u][v] -= w
        matrix[v][u] -= w
        graph[u].add(v)
        graph[v].add(u)
    seen, queue = set(range(b)), list(range(b))
    for u in queue:
        for v in graph[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if len(seen) != vertices:
        raise ValueError("an energy vertex has no path to a grounded anchor")
    if any(inverse[i][j] != inverse[j][i] for i in range(n) for j in range(n)):
        raise ValueError("ground inverse is not symmetric")
    for i in range(n):
        for j in range(n):
            if sum(matrix[b + i][b + k] * inverse[k][j] for k in range(n)) != (den if i == j else 0):
                raise ValueError("exact full-type integer ground inverse failed")
    harmonic = [[-sum(inverse[i][k] * matrix[b + k][j] for k in range(n))
                 for j in range(b)] for i in range(n)]
    if any(min(row) < 0 or sum(row) != den for row in harmonic):
        raise ValueError("full-type harmonic extension is not an exact convex combination")
    schur = [[matrix[i][j] * den + sum(matrix[i][b + k] * harmonic[k][j] for k in range(n))
              for j in range(b)] for i in range(b)]
    if (any(sum(row) for row in schur)
            or any(schur[i][j] != schur[j][i] for i in range(b) for j in range(b))
            or any(schur[i][j] > 0 for i in range(b) for j in range(b) if i != j)):
        raise ValueError("invalid full-type Schur energy or pair weights")
    return {"spec": spec, "B": b, "vertices": vertices, "edges": edges,
            "weights": weights, "scale": scale, "matrix": matrix,
            "inverse": inverse, "inverse_denominator": den, "harmonic": harmonic,
            "energy_denominator": scale * den,
            "pairs": [(i, j, -schur[i][j]) for i in range(b)
                      for j in range(i + 1, b) if schur[i][j]]}


def cosine_lower(lo, hi, arcs):
    lo, hi = F(lo), F(hi)
    if lo > hi:
        raise ValueError("empty pair-difference interval")
    # cos(2*pi*t) has minima exactly at the half-integers.
    shifted_lo, shifted_hi = lo - F(1, 2), hi - F(1, 2)
    first = -((-shifted_lo.numerator) // shifted_lo.denominator)
    last = shifted_hi.numerator // shifted_hi.denominator
    if first <= last:
        return -arcs.SCALE
    return min(arcs.sincos_turn(lo)[0][0], arcs.sincos_turn(hi)[0][0])


def hessian_minorant(kernel, matrix, lower, upper, arcs):
    b, n = kernel["B"], kernel["B"] - 1
    lower, upper = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if (len(lower) != b or len(upper) != b or len(matrix) != b
            or any(len(row) != b for row in matrix)
            or any(a > c for a, c in zip(lower, upper))):
        raise ValueError("invalid quadratic whole-box domain")
    nums = [[0] * n for _ in range(n)]
    for i, j, weight in kernel["pairs"]:
        lo = max(lower[j] - upper[i], -F(matrix[j][i], SCALE))
        hi = min(upper[j] - lower[i], F(matrix[i][j], SCALE))
        cosine = cosine_lower(lo, hi, arcs)
        pi_bound = arcs.PI[0] if cosine >= 0 else arcs.PI[1]
        coefficient = 8 * pi_bound**2 * weight * cosine
        if i:
            nums[i - 1][i - 1] += coefficient
        if j:
            nums[j - 1][j - 1] += coefficient
        if i and j:
            nums[i - 1][j - 1] -= coefficient
            nums[j - 1][i - 1] -= coefficient
    den = kernel["energy_denominator"] * arcs.SCALE**3
    rounded = [[F(x * ROUND_GRID // den, ROUND_GRID) for x in row] for row in nums]
    if any(not 0 <= F(nums[i][j], den) - rounded[i][j] < F(1, ROUND_GRID)
           for i in range(n) for j in range(n)):
        raise AssertionError("quadratic Hessian grid error was not outward bounded")
    return rounded


def positive_ldl(matrix):
    n = len(matrix)
    if not n or any(len(row) != n for row in matrix):
        raise ValueError("invalid curvature matrix dimensions")
    if any(matrix[i][j] != matrix[j][i] for i in range(n) for j in range(n)):
        raise ValueError("curvature matrix is not symmetric")
    lower = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    pivots = []
    for i in range(n):
        pivot = matrix[i][i] - sum(lower[i][k]**2 * pivots[k] for k in range(i))
        if pivot <= 0:
            raise ValueError("exact curvature LDL is not strictly positive")
        pivots.append(pivot)
        for j in range(i + 1, n):
            lower[j][i] = (matrix[j][i] - sum(lower[j][k] * lower[i][k] * pivots[k]
                                             for k in range(i))) / pivot
    if any(sum(lower[i][k] * pivots[k] * lower[j][k] for k in range(n)) != matrix[i][j]
           for i in range(n) for j in range(n)):
        raise AssertionError("fresh exact curvature LDL reconstruction failed")
    return pivots


def curvature_gate(kernel, matrix, lower, upper, eta, arcs):
    n = kernel["B"] - 1
    diagonal = list(map(F, eta)) if isinstance(eta, list) else [F(eta)] * n
    if len(diagonal) != n or any(not 0 <= x <= 10**60 for x in diagonal):
        raise ValueError("invalid negative-curvature allowance")
    rounded = hessian_minorant(kernel, matrix, lower, upper, arcs)
    n = len(rounded)
    # A symmetric entrywise error <1/grid has operator norm <=n/grid.
    test = [[value + (diagonal[i] - F(n, ROUND_GRID) if i == j else 0)
             for j, value in enumerate(row)] for i, row in enumerate(rounded)]
    positive_ldl(test)
    return {"negative_curvature_allowance": list(map(str, diagonal)) if isinstance(eta, list) else str(F(eta)),
            "exact_positive_LDL_and_full_reconstruction_checked": True,
            "symmetric_Hessian_rounding_spectral_error_charged": str(F(n, ROUND_GRID)),
            "all_pair_difference_intervals_use_closed_box_and_necessary_matrix": True}


def reference_gate(reference, lower, upper, matrix):
    b = len(matrix)
    ref = [F(0), *map(F, reference)]
    lo, hi = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if (len(ref) != b or len(lo) != b or len(hi) != b
            or any(not a <= x <= c for x, a, c in zip(ref, lo, hi))
            or any(ref[j] - ref[i] > F(matrix[i][j], SCALE) for i in range(b) for j in range(b))):
        raise ValueError("energy reference is outside the exact closed feasible domain")
    return ref, lo, hi


def point_energy_gradient(kernel, reference, arcs):
    b, scale = kernel["B"], arcs.SCALE
    energy_num, g_lo, g_hi = 0, [0] * b, [0] * b
    for i, j, weight in kernel["pairs"]:
        co, si = arcs.sincos_turn(reference[j] - reference[i])
        energy_num += 2 * weight * (scale - co[1])
        g_lo[i] -= weight * si[1]
        g_hi[i] -= weight * si[0]
        g_lo[j] += weight * si[0]
        g_hi[j] += weight * si[1]
    energy = F(energy_num, kernel["energy_denominator"] * scale)
    gradient = []
    for a, c in zip(g_lo, g_hi):
        products = [p * x for p in arcs.PI for x in (a, c)]
        gradient.append((F(4 * min(products), kernel["energy_denominator"] * scale**2),
                         F(4 * max(products), kernel["energy_denominator"] * scale**2)))
    return energy, gradient


def linear_support(reference, lower, upper, matrix, gradient, dual):
    b, q = len(reference), dual["q"]
    terms = dual["terms"]
    if type(q) is not int or not 0 < q <= 10**60 or not isinstance(terms, list):
        raise ValueError("invalid quadratic linear dual scale")
    seen, divergence, constant = set(), [F(0)] * b, F(0)
    for item in terms:
        if (not isinstance(item, list) or len(item) != 3
                or any(type(i) is not int or not 0 <= i < b for i in item[:2])
                or item[0] == item[1]):
            raise ValueError("invalid quadratic difference dual indices")
        i, j, raw = item
        numerator = int(raw)
        if numerator < 0 or numerator.bit_length() > 800 or (i, j) in seen:
            raise ValueError("negative or duplicate quadratic difference multiplier")
        seen.add((i, j))
        mu = F(numerator, q)
        divergence[i] -= mu
        divergence[j] += mu
        constant += mu * (reference[j] - reference[i] - F(matrix[i][j], SCALE))
    residual, charge = [], F(0)
    for k in range(1, b):
        interval = [x + divergence[k] for x in gradient[k]]
        delta = [lower[k] - reference[k], upper[k] - reference[k]]
        value = min(x * y for x in interval for y in delta)
        residual.append(value)
        charge += value
    return constant + charge, {
        "nonnegative_difference_dual_terms": len(terms),
        "exact_dual_divergence_and_all_gradient_interval_residuals_charged": True}


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    if (set(certificate) not in ({"reference_turns", "eta", "difference_dual"},
                                {"reference_turns", "eta", "difference_dual", "curvature_mode"})
            or certificate.get("curvature_mode", "constant-max-square") not in
               ("constant-max-square", "box-secant")):
        raise ValueError("quadratic payment has unknown or missing fields")
    ref, lo, hi = reference_gate(certificate["reference_turns"], lower, upper, matrix)
    curvature = curvature_gate(kernel, matrix, lower, upper, certificate["eta"], arcs)
    reference_energy, gradient = point_energy_gradient(kernel, ref, arcs)
    diagonal = list(map(F, certificate["eta"])) if isinstance(certificate["eta"], list) else [
        F(certificate["eta"])] * (kernel["B"] - 1)
    mode = certificate.get("curvature_mode", "constant-max-square")
    if mode == "box-secant":
        shifted = list(gradient)
        correction = F(0)
        for k, allowance in enumerate(diagonal, 1):
            a, c = lo[k] - ref[k], hi[k] - ref[k]
            slope = allowance * (a + c) / 2
            shifted[k] = tuple(g - slope for g in gradient[k])
            correction += allowance * a * c / 2
        support, dual_check = linear_support(ref, lo, hi, matrix, shifted, certificate["difference_dual"])
        remainder = -correction
    else:
        support, dual_check = linear_support(ref, lo, hi, matrix, gradient, certificate["difference_dual"])
        remainder = sum(allowance * max(abs(lo[k] - ref[k]), abs(hi[k] - ref[k]))**2 / 2
                        for k, allowance in enumerate(diagonal, 1))
    lower_energy = reference_energy + support - remainder
    upper_energy = F(radius)**2 * F(sum(kernel["weights"]), kernel["scale"])
    margin = lower_energy - upper_energy
    normalized = max(F(0), lower_energy) / F(sum(kernel["weights"]), kernel["scale"])
    root_scale = 10**100
    root_num = isqrt(normalized.numerator * root_scale**2 // normalized.denominator)
    radius_lower = F(root_num, root_scale)
    if not radius_lower**2 <= normalized < (radius_lower + F(1, root_scale))**2:
        raise AssertionError("exact outward radius conversion failed")
    radius_margin = radius_lower - F(radius)
    if margin > 0 and radius_margin <= 0:
        raise ValueError("strict energy payment needs a finer rational radius endpoint")
    return {
        "boundary_quadratic_energy_lower": str(lower_energy),
        "same_root_whole_rod_energy_upper": str(upper_energy),
        "minimum_strict_energy_margin": str(margin),
        "radius_at_most_Rstar_whole_box_excluded": margin > 0,
        "required_radius_lower": str(radius_lower),
        "minimum_strict_radius_margin": str(radius_margin),
        "energy_to_radius_conversion_square_identity_checked": True,
        "reference_energy_lower": str(reference_energy),
        "exact_linear_support_lower": str(support),
        "entire_closed_box_negative_curvature_remainder": str(remainder),
        "curvature_remainder_mode": mode,
        "reference_inside_exact_box_and_every_difference_constraint": True,
        "convexity_of_original_angular_energy_not_assumed": True,
        **curvature, **dual_check}
