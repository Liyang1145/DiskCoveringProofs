"""Discovery-only curvature search with outward common-denominator diagonals."""

from fractions import Fraction as F
from math import ceil

import numpy as np
from scipy.optimize import minimize

import n26_quadratic_energy_minorant as exact
from propose_quadratic_energy_minorant import rational_reference
from propose_quadratic_secant_refinement import dual


GRID = 10**12


def upward_grid(value):
    value = F(value)
    return F(-((-value.numerator * GRID) // value.denominator), GRID)


def refine(kernel, matrix, box, angles, radius, arcs):
    lower, upper = box["lower"], box["upper"]
    reference = rational_reference(angles, lower, upper, matrix)
    ref, lo, hi = exact.reference_gate(reference, lower, upper, matrix)
    hessian = exact.hessian_minorant(kernel, matrix, lower, upper, arcs)
    h = np.array([[float(value) for value in row] for row in hessian])
    widths = [max(abs(a - x), abs(b - x), F(1, 10**10))
              for a, b, x in zip(lo[1:], hi[1:], ref[1:])]
    width = np.array(list(map(float, widths)))
    scalar = F(ceil(max(0., -float(np.linalg.eigvalsh(h)[0]) + 1e-9) * GRID), GRID)
    transformed = h * width[:, None] * width[None, :]
    weighted_eta = F(ceil(max(0., -float(np.linalg.eigvalsh(transformed)[0]) + 1e-12) * GRID), GRID)
    weighted = [upward_grid(weighted_eta / value**2) for value in widths]
    start = np.array(list(map(float, weighted)))
    costs = width**2 / max(width**2)

    def spectral(values):
        eigenvalues, eigenvectors = np.linalg.eigh(h + np.diag(values))
        return float(eigenvalues[0]) - 1e-9, eigenvectors[:, 0]**2

    optimized = minimize(lambda x: float(costs @ x), start, jac=lambda x: costs,
                         bounds=[(0., None)] * len(start),
                         constraints={"type": "ineq", "fun": lambda x: spectral(x)[0],
                                      "jac": lambda x: spectral(x)[1]},
                         method="SLSQP", options={"ftol": 1e-12, "maxiter": 160, "disp": False})
    diagonal = [F(ceil(max(0., float(value) + 1e-8) * GRID), GRID) for value in optimized.x]
    _, gradient = exact.point_energy_gradient(kernel, ref, arcs)
    candidates = []
    for label, proposal in (("common-grid-scalar", [scalar] * len(widths)),
                            ("outward-common-grid-width-normalized", weighted),
                            ("common-grid-optimized", diagonal)):
        proposal = list(proposal)
        for _ in range(6):
            try:
                exact.curvature_gate(kernel, matrix, lower, upper, proposal, arcs)
            except ValueError:
                proposal = [upward_grid(value * F(101, 100) + F(1, 10**8)) for value in proposal]
            else:
                break
        else:
            continue
        for mode in ("constant-max-square", "box-secant"):
            certificate = {"reference_turns": reference, "eta": list(map(str, proposal)),
                           "curvature_mode": mode,
                           "difference_dual": dual(kernel, matrix, ref, lo, hi, gradient, proposal, mode)}
            checked = exact.bound(kernel, matrix, lower, upper, certificate, radius, arcs)
            candidates.append((certificate, checked, label))
    if not candidates:
        raise ValueError("common-grid candidate curvature proposal did not pass exact arithmetic")
    return max(candidates, key=lambda item: F(item[1]["minimum_strict_energy_margin"]))
