"""Distinct B17 inward-owner energy kernel; arithmetic only, not admission.

The extra origin weight is a Lagrange multiplier, NOT a rho-bounded rod.
Consequently Schur row sums need not vanish and must not be discarded.
"""

from fractions import Fraction as F

import n26_partial_prefix_quadratic_kernel as partial
from n26_force import D
from n26_pairwise_affine_energy import GRID, pair_lines, value_interval


SCHEMA = "N26-B17-inward-owner-origin-ground-kernel-v1"
AFFINE_MODE = "N26-B17-origin-kernel-pairwise-affine-domain-v1"
KAPPA = F(165933607, 207000000)
ALPHA = F(9, 200)


def matrix_from_weights(spec, weights, origin_weight, owner):
    vertices, edges = partial.graph(spec)
    if (spec["B"] != 17 or type(owner) is not int or not 0 <= owner < 17
            or len(weights) != len(edges)
            or any(type(w) is not int or not 0 < w or w.bit_length() > 800 for w in weights)
            or type(origin_weight) is not int or not 0 <= origin_weight
            or origin_weight.bit_length() > 800):
        raise ValueError("invalid distinct B17 original rods or origin multiplier")
    matrix = [[0] * vertices for _ in range(vertices)]
    adjacency = [set() for _ in range(vertices)]
    for (u, v), w in zip(edges, weights):
        matrix[u][u] += w
        matrix[v][v] += w
        matrix[u][v] -= w
        matrix[v][u] -= w
        adjacency[u].add(v)
        adjacency[v].add(u)
    seen, queue = set(range(17)), list(range(17))
    for u in queue:
        for v in adjacency[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if len(seen) != vertices:
        raise ValueError("an original free vertex is not grounded by original rods")
    matrix[17 + owner][17 + owner] += origin_weight
    return vertices, edges, matrix


def kernel_gate(spec, certificate):
    fields = {"schema", "spec", "owner", "kappa", "weight_scale", "weight_numerators",
              "origin_weight_numerator", "inverse_denominator", "inverse_numerators"}
    if (set(certificate) != fields or certificate["schema"] != SCHEMA
            or certificate["spec"] != spec or F(certificate["kappa"]) != KAPPA
            or type(certificate["weight_scale"]) is not int
            or not 0 < certificate["weight_scale"] <= 10**60):
        raise ValueError("wrong B17 radial kernel schema, source or inward bound")
    scale, owner = certificate["weight_scale"], certificate["owner"]
    weights, mu = certificate["weight_numerators"], certificate["origin_weight_numerator"]
    vertices, edges, matrix = matrix_from_weights(spec, weights, mu, owner)
    free = vertices - 17
    den = int(certificate["inverse_denominator"])
    inverse = [[int(v) for v in row] for row in certificate["inverse_numerators"]]
    if (den <= 0 or len(inverse) != free or any(len(row) != free for row in inverse)
            or any(inverse[i][j] != inverse[j][i] for i in range(free) for j in range(free))):
        raise ValueError("wrong distinct origin-ground inverse size/sign/symmetry")
    for i in range(free):
        for j in range(free):
            if sum(matrix[17+i][17+k]*inverse[k][j] for k in range(free)) != (
                    den if i == j else 0):
                raise ValueError("fresh exact origin-ground inverse identity failed")
    extension = [[-sum(inverse[i][k]*matrix[17+k][j] for k in range(free))
                  for j in range(17)] for i in range(free)]
    if any(min(row) < 0 or not 0 <= sum(row) <= den for row in extension):
        raise ValueError("origin-ground extension is not a substochastic anchor combination")
    schur = [[matrix[i][j]*den+sum(matrix[i][17+k]*extension[k][j] for k in range(free))
              for j in range(17)] for i in range(17)]
    row_sums = [sum(row) for row in schur]
    if (min(row_sums) < 0
            or any(schur[i][j] != schur[j][i] for i in range(17) for j in range(17))
            or any(schur[i][j] > 0 for i in range(17) for j in range(17) if i != j)
            or (mu == 0 and any(row_sums)) or (mu > 0 and sum(row_sums) <= 0)):
        raise ValueError("origin-ground Schur pair/row-sum identity failed")
    return {
        "spec": spec, "B": 17, "vertices": vertices, "edges": edges,
        "weights": weights, "scale": scale, "owner": owner, "origin_weight": mu,
        "matrix": matrix, "inverse": inverse, "inverse_denominator": den,
        "extension": extension, "schur": schur, "row_sums": row_sums,
        "pairs": [(i, j, -schur[i][j]) for i in range(17)
                  for j in range(i+1, 17) if schur[i][j]],
        "origin_ground_mode_distinct_from_old_harmonic_kernels": True,
    }


def identity_control(kernel):
    """Exact nonunit anchors make the otherwise hidden row-sum term visible."""
    den, scale, count = kernel["inverse_denominator"], kernel["scale"], kernel["vertices"]-17
    anchors = [[F((3*i+1) % 7-3), F((5*i+2) % 11-5)] for i in range(17)]
    free = [[F((7*i+3) % 13-6), F((11*i+4) % 17-8)] for i in range(count)]
    points = anchors + free
    direct = sum(F(w, scale)*sum((points[u][d]-points[v][d])**2 for d in range(2))
                 for (u, v), w in zip(kernel["edges"], kernel["weights"]))
    direct += F(kernel["origin_weight"], scale)*sum(v*v for v in free[kernel["owner"]])
    boundary = sum(F(w, scale*den)*sum((anchors[i][d]-anchors[j][d])**2 for d in range(2))
                   for i, j, w in kernel["pairs"])
    boundary += sum(F(w, scale*den)*sum(v*v for v in anchors[i])
                    for i, w in enumerate(kernel["row_sums"]))
    deviation = [[free[i][d]-sum(F(kernel["extension"][i][j], den)*anchors[j][d]
                                for j in range(17)) for d in range(2)] for i in range(count)]
    residual = sum(F(kernel["matrix"][17+i][17+j], scale)*
                   sum(deviation[i][d]*deviation[j][d] for d in range(2))
                   for i in range(count) for j in range(count))
    if direct != boundary+residual or residual < 0:
        raise ValueError("origin-ground independent square completion failed")
    return {
        "nonunit_anchor_nonharmonic_free_exact_square_completion_checked": True,
        "nonzero_row_sum_term_retained": kernel["origin_weight"] > 0,
        "original_positive_rods_prove_ground_positive_definiteness": True,
        "origin_multiplier_NOT_counted_as_rho_bounded_rod": True,
    }


def constant(kernel):
    den, weights = kernel["inverse_denominator"], sum(kernel["weights"])
    return F(sum(kernel["row_sums"]), den*weights)-F(
        kernel["origin_weight"], weights)*KAPPA**2


def point_interval(kernel, turns, arcs):
    lower = upper = constant(kernel)
    for i, j, w in kernel["pairs"]:
        a, b = value_interval(F(turns[j])-F(turns[i]), arcs)
        coefficient = F(w, kernel["inverse_denominator"]*sum(kernel["weights"]))
        lower += coefficient*a
        upper += coefficient*b
    return lower, upper


def prepare(kernel, matrix, arcs):
    if (kernel.get("origin_ground_mode_distinct_from_old_harmonic_kernels") is not True
            or len(matrix) != 17 or any(len(row) != 17 for row in matrix)
            or any(matrix[i][i] != 0 for i in range(17))):
        raise ValueError("wrong distinct radial closed angular domain")
    lo = [F(-matrix[j][0], D) for j in range(17)]
    hi = [F(matrix[0][j], D) for j in range(17)]
    terms = []
    for i, j, w in kernel["pairs"]:
        a, b = -F(matrix[j][i], D), F(matrix[i][j], D)
        coefficient = F(w, kernel["inverse_denominator"]*sum(kernel["weights"]))
        terms.append((i, j, coefficient, a, b, pair_lines(a, b, arcs)))
    return lo, hi, terms, constant(kernel)


def exact_bound(data, matrix, certificate, radius):
    lo, hi, terms, additive = data
    if (set(certificate) != {"mode", "pair_line_mixture_numerators",
                             "difference_dual_denominator", "difference_dual_terms"}
            or certificate["mode"] != AFFINE_MODE
            or certificate["difference_dual_denominator"] != GRID
            or len(certificate["pair_line_mixture_numerators"]) != len(terms)):
        raise ValueError("invalid B17 origin affine certificate")
    gradient, total = [F(0)]*17, additive
    for term, mixture in zip(terms, certificate["pair_line_mixture_numerators"]):
        i, j, coefficient, _, _, lines = term
        if (len(mixture) != len(lines) or sum(mixture) <= 0
                or any(type(v) is not int or not 0 <= v <= 10**18 for v in mixture)):
            raise ValueError("invalid exact normalized nonnegative pair-line mixture")
        denominator = sum(mixture)
        slope = sum(F(n, denominator)*line[0] for n, line in zip(mixture, lines))
        intercept = sum(F(n, denominator)*line[1] for n, line in zip(mixture, lines))
        gradient[i] -= coefficient*slope
        gradient[j] += coefficient*slope
        total += coefficient*intercept
    seen = set()
    for row in certificate["difference_dual_terms"]:
        if (not isinstance(row, list) or len(row) != 3 or any(type(v) is not int for v in row)
                or not 0 <= row[0] < 17 or not 0 <= row[1] < 17 or row[0] == row[1]
                or not 0 <= row[2] <= 10**24 or tuple(row[:2]) in seen):
            raise ValueError("invalid exact nonnegative original-difference dual")
        i, j, n = row
        seen.add((i, j))
        gradient[i] -= F(n, GRID)
        gradient[j] += F(n, GRID)
        total -= F(n, GRID)*F(matrix[i][j], D)
    lower = total+sum(min(g*a, g*b) for g, a, b in zip(gradient, lo, hi))
    return {
        "normalized_radial_branch_entire_domain_energy_lower": str(lower),
        "original_rod_weight_normalized_radius_squared_cap": str(F(radius)**2),
        "exact_strict_energy_margin": str(lower-F(radius)**2),
        "arithmetic_strict_entire_radial_branch": lower > F(radius)**2,
        "origin_multiplier_and_all_Schur_row_sums_retained": True,
        "original_rod_weights_ONLY_in_radius_cap": True,
        "new_geometric_payments": 0,
    }


def suggest(data, matrix, radius):
    import numpy as np
    from scipy.optimize import linprog

    lo, hi, terms, additive = data
    count = 16+len(terms)
    objective, rows, rhs, slices = np.zeros(count), [], [], []
    for index, (i, j, coefficient, _, _, lines) in enumerate(terms):
        objective[16+index] = float(coefficient)
        start = len(rows)
        for slope, intercept in lines:
            row = np.zeros(count)
            if i:
                row[i-1] -= float(slope)
            if j:
                row[j-1] += float(slope)
            row[16+index] = -1
            rows.append(row)
            rhs.append(-float(intercept))
        slices.append((start, len(rows)))
    difference_rows = []
    for i in range(17):
        for j in range(17):
            if i == j:
                continue
            row = np.zeros(count)
            if i:
                row[i-1] -= 1
            if j:
                row[j-1] += 1
            difference_rows.append((i, j, len(rows)))
            rows.append(row)
            rhs.append(float(F(matrix[i][j], D)))
    optimized = linprog(
        objective, A_ub=np.array(rows), b_ub=np.array(rhs),
        bounds=[(float(a), float(b)) for a, b in zip(lo[1:], hi[1:])]
        + [(None, None)]*len(terms), method="highs")
    if not optimized.success:
        return None, None, {"numerical_LP_success_NOT_proof": False,
                            "message": str(optimized.message)}
    marginal = optimized.ineqlin.marginals
    mixtures = []
    for (_, _, coefficient, a, b, lines), (start, end) in zip(terms, slices):
        mixture = [max(0, round(-float(v)/float(coefficient)*GRID)) for v in marginal[start:end]]
        if not sum(mixture):
            best = max(range(len(lines)), key=lambda k: lines[k][0]*(a+b)/2+lines[k][1])
            mixture[best] = GRID
        mixtures.append(mixture)
    dual = [[i, j, max(0, round(-float(marginal[index])*GRID))]
            for i, j, index in difference_rows if -float(marginal[index]) > 0]
    certificate = {"mode": AFFINE_MODE, "pair_line_mixture_numerators": mixtures,
                   "difference_dual_denominator": GRID, "difference_dual_terms": dual}
    return certificate, exact_bound(data, matrix, certificate, radius), {
        "numerical_LP_success_NOT_proof": True,
        "numerical_normalized_lower_NOT_proof": float(optimized.fun)+float(additive),
    }
