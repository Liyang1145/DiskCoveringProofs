"""Exact closed-domain pairwise affine minorants; arithmetic, not admission."""

from fractions import Fraction as F
from math import isqrt

import numpy as np
from scipy.optimize import linprog

from n26_sharp_radius_constraints import SCALE
from n26_quadratic_energy_minorant import cosine_lower


MODE = "N26-full134rod-pairwise-affine-closed-domain-v1"
GRID = 10**12


def cosine_upper(a, b, arcs):
    if a > b:
        raise ValueError("empty pair interval")
    first = -((-a.numerator) // a.denominator)
    last = b.numerator // b.denominator
    if first <= last:
        return arcs.SCALE
    return max(arcs.sincos_turn(a)[0][1], arcs.sincos_turn(b)[0][1])


def value_interval(x, arcs):
    cosine, _ = arcs.sincos_turn(x)
    return F(2*(arcs.SCALE-cosine[1]), arcs.SCALE), F(
        2*(arcs.SCALE-cosine[0]), arcs.SCALE)


def derivative_interval(x, arcs):
    _, sine = arcs.sincos_turn(x)
    products = [4*pi*s for pi in arcs.PI for s in sine]
    return F(min(products), arcs.SCALE**2), F(max(products), arcs.SCALE**2)


def pair_lines(a, b, arcs):
    """Every returned (slope, intercept) is below 2(1-cos(2*pi*x))."""
    a, b = F(a), F(b)
    if a > b:
        raise ValueError("empty necessary difference interval")
    if a == b:
        return [(F(0), value_interval(a, arcs)[0])]
    if cosine_upper(a, b, arcs) <= 0:
        left, right = value_interval(a, arcs)[0], value_interval(b, arcs)[0]
        slope = (right-left)/(b-a)
        return [(slope, left-slope*a)]
    cosine = cosine_lower(a, b, arcs)
    pi = arcs.PI[0] if cosine >= 0 else arcs.PI[1]
    curvature = F(8*pi*pi*cosine, arcs.SCALE**3)
    result = []
    for numerator in range(5):
        reference = a+(b-a)*F(numerator, 4)
        value = value_interval(reference, arcs)[0]
        low, high = derivative_interval(reference, arcs)
        slope = (low+high)/2
        error = (high-low)/2*max(reference-a, b-reference)
        intercept = value-slope*reference-error
        if curvature < 0:
            slope += curvature*(a+b-2*reference)/2
            intercept += curvature*(reference*reference-a*b)/2
        result.append((slope, intercept))
    return list(dict.fromkeys(result))


def prepare(kernel, matrix, lower, upper, arcs):
    if (kernel.get("distinct_full134rod_60free_positive_candidate_kernel") is not True
            or kernel["B"] != 16 or kernel["vertices"] != 76
            or len(kernel["weights"]) != 134):
        raise ValueError("this experiment requires the distinct full134rod kernel")
    lo, hi = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if (len(lo) != 16 or len(hi) != 16 or len(matrix) != 16
            or any(len(row) != 16 for row in matrix)
            or any(a > b for a, b in zip(lo, hi))):
        raise ValueError("invalid entire closed angular box")
    terms = []
    for i, j, numerator in kernel["pairs"]:
        if numerator <= 0:
            raise ValueError("Schur pair coefficient must be positive")
        a = max(lo[j]-hi[i], -F(matrix[j][i], SCALE))
        b = min(hi[j]-lo[i], F(matrix[i][j], SCALE))
        coefficient = F(numerator, kernel["inverse_denominator"]*sum(kernel["weights"]))
        terms.append((i, j, coefficient, a, b, pair_lines(a, b, arcs)))
    return lo, hi, terms


def exact_bound(data, matrix, certificate, radius):
    lo, hi, terms = data
    if (certificate.get("mode") != MODE
            or len(certificate.get("pair_line_mixture_numerators", [])) != len(terms)
            or certificate.get("difference_dual_denominator") != GRID):
        raise ValueError("wrong pairwise arithmetic certificate shape")
    gradient, constant = [F(0)]*16, F(0)
    for term, mixture in zip(terms, certificate["pair_line_mixture_numerators"]):
        i, j, coefficient, _, _, lines = term
        if (len(mixture) != len(lines)
                or any(type(n) is not int or not 0 <= n <= 10**18 for n in mixture)
                or sum(mixture) <= 0):
            raise ValueError("invalid nonnegative normalized pair-line mixture")
        denominator = sum(mixture)
        slope = sum(F(n, denominator)*line[0] for n, line in zip(mixture, lines))
        intercept = sum(F(n, denominator)*line[1] for n, line in zip(mixture, lines))
        gradient[i] -= coefficient*slope
        gradient[j] += coefficient*slope
        constant += coefficient*intercept
    seen = set()
    for row in certificate["difference_dual_terms"]:
        if (not isinstance(row, list) or len(row) != 3
                or any(type(n) is not int for n in row)
                or not 0 <= row[0] < 16 or not 0 <= row[1] < 16
                or row[0] == row[1] or not 0 <= row[2] <= 10**24
                or tuple(row[:2]) in seen):
            raise ValueError("invalid nonnegative necessary-difference multiplier")
        i, j, numerator = row
        seen.add((i, j))
        multiplier = F(numerator, GRID)
        gradient[i] -= multiplier
        gradient[j] += multiplier
        constant -= multiplier*F(matrix[i][j], SCALE)
    lower = constant+sum(min(g*a, g*b) for g, a, b in zip(gradient, lo, hi))
    square = max(F(0), lower)
    radius_grid = 10**100
    outward = F(isqrt(square.numerator*radius_grid**2//square.denominator), radius_grid)
    if not outward**2 <= square < (outward+F(1, radius_grid))**2:
        raise AssertionError("outward square root failed")
    return {
        "normalized_closed_box_energy_lower": str(lower),
        "normalized_same_root_energy_cap": str(F(radius)**2),
        "strict_energy_margin": str(lower-F(radius)**2),
        "strict_radius_margin": str(outward-F(radius)),
        "arithmetic_strict_entire_closed_leaf": lower > F(radius)**2 and outward > F(radius),
        "all_pair_line_mixtures_exactly_nonnegative_and_normalized": True,
        "all_necessary_difference_multipliers_exactly_nonnegative": True,
        "geometry_admission_performed": False,
        "new_geometric_payments": 0,
    }


def suggest(data, matrix, radius):
    """Numerical LP provides only multipliers; exact_bound makes the decision."""
    lo, hi, terms = data
    variables = 15+len(terms)
    rows, right, slices = [], [], []
    objective = np.zeros(variables)
    for index, (i, j, coefficient, _, _, lines) in enumerate(terms):
        objective[15+index] = float(coefficient)
        start = len(rows)
        for slope, intercept in lines:
            row = np.zeros(variables)
            if i:
                row[i-1] -= float(slope)
            if j:
                row[j-1] += float(slope)
            row[15+index] = -1
            rows.append(row)
            right.append(-float(intercept))
        slices.append((start, len(rows)))
    difference_rows = []
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            row = np.zeros(variables)
            if i:
                row[i-1] -= 1
            if j:
                row[j-1] += 1
            difference_rows.append((i, j, len(rows)))
            rows.append(row)
            right.append(float(F(matrix[i][j], SCALE)))
    optimized = linprog(
        objective, A_ub=np.array(rows), b_ub=np.array(right),
        bounds=[(float(a), float(b)) for a, b in zip(lo[1:], hi[1:])]
        + [(None, None)]*len(terms), method="highs")
    if not optimized.success:
        return None, None, {"numerical_LP_success_NOT_proof": False,
                            "message": str(optimized.message)}
    marginal = optimized.ineqlin.marginals
    mixtures = []
    for (_, _, coefficient, a, b, lines), (start, end) in zip(terms, slices):
        mixture = [max(0, round(-float(value)/float(coefficient)*GRID))
                   for value in marginal[start:end]]
        if sum(mixture) == 0:
            reference = (a+b)/2
            best = max(range(len(lines)), key=lambda k: lines[k][0]*reference+lines[k][1])
            mixture[best] = GRID
        mixtures.append(mixture)
    dual = []
    for i, j, index in difference_rows:
        numerator = max(0, round(-float(marginal[index])*GRID))
        if numerator:
            dual.append([i, j, numerator])
    certificate = {
        "mode": MODE,
        "pair_line_mixture_numerators": mixtures,
        "difference_dual_denominator": GRID,
        "difference_dual_terms": dual,
    }
    return certificate, exact_bound(data, matrix, certificate, radius), {
        "numerical_LP_success_NOT_proof": True,
        "numerical_normalized_energy_NOT_proof": float(optimized.fun),
    }


def independent_point_checks(data, arcs):
    lo, hi, terms = data
    checked = 0
    for i, j, coefficient, a, b, lines in terms:
        for x in (a, (a+b)/2, b):
            upper = value_interval(x, arcs)[1]
            if any(slope*x+intercept > upper for slope, intercept in lines):
                raise AssertionError("pair minorant exceeds independently bounded function value")
            checked += len(lines)
    return checked
