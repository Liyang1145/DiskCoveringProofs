"""Broader numerical positive supports, followed by FRESH exact reconstruction.

This module proposes DATA only. No source/model admission or geometry payment
is performed, and no old support or forest is changed.
"""

from copy import deepcopy
from fractions import Fraction as F

import numpy as np
from scipy.optimize import minimize
from sympy import Matrix

import n26_reweighted_candidate_energy as alternative
import probe_candidate_reweighted_point_energy as old_numerical


def exact_support(original, kernel, point, weights):
    weights = np.maximum(np.array(weights, dtype=float), 1e-30)
    if np.any(~np.isfinite(weights)) or weights.sum() <= 0:
        raise ValueError("broad suggestion has nonfinite or nonpositive weights")
    weights /= weights.sum()
    scale = 10**30
    integers = [max(1, round(float(value)*scale)) for value in weights]
    reference = deepcopy(original["reference"])
    reference.update(rational_scale=str(scale), weight_numerators=list(map(str, integers)),
                     alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=True)
    laplacian = alternative.dirichlet.laplacian(kernel["edges"], integers)
    inverse, denominator = Matrix([row[16:] for row in laplacian[16:]]).to_DM().inv_den()
    numbers = [[int(value) for value in row] for row in inverse.to_Matrix().tolist()]
    denominator = int(denominator)
    if denominator < 0:
        numbers, denominator = [[-value for value in row] for row in numbers], -denominator
    certificate = {
        "schema": "N26-exact-integer-ground-Dirichlet-inverse-v1", "anchor_vertices": 16,
        "inverse_denominator": str(denominator),
        "inverse_numerators": [[str(value) for value in row] for row in numbers],
    }
    checked = alternative.kernel_gate(original["reference"], reference, certificate)
    return {
        "mode": "NEW-POSITIVE-SUPPORT", "reference": reference, "inverse": certificate,
        "suggestion_point_turns": list(map(str, point)),
    }, checked


def suggest(original, kernel, point, iterations=180, log_spread=3.0, simplex_floor=1e-9):
    if (type(iterations) is not int or not 1 <= iterations <= 1000
            or not 0 < log_spread <= 6 or not 0 < simplex_floor < 1/92):
        raise ValueError("invalid broader numerical support limits")
    edges = kernel["edges"]
    anchors = np.array([[np.cos(2*np.pi*float(turn)), np.sin(2*np.pi*float(turn))]
                        for turn in [F(0), *point]])
    start = np.array(kernel["weights"], dtype=float)
    start /= start.sum()
    base, _ = old_numerical.float_energy(edges, start, anchors)
    cap = float(F(original["radius"])**2)

    def logarithmic(shift):
        weights = start*np.exp(shift)
        weights /= weights.sum()
        value, squared = old_numerical.float_energy(edges, weights, anchors)
        return -(value-base)*10**8, -weights*(squared-value)*10**8

    log_result = minimize(
        logarithmic, np.zeros(92), jac=True, method="L-BFGS-B",
        bounds=[(-log_spread, log_spread)]*92,
        options={"maxiter": iterations, "ftol": 1e-15, "gtol": 1e-9, "maxls": 50})
    log_weights = start*np.exp(log_result.x)
    log_weights /= log_weights.sum()

    def simplex(weights):
        value, squared = old_numerical.float_energy(edges, weights, anchors)
        # Subtracting cap*sum(weights) does not change the simplex optimum.
        return -(value-cap*weights.sum())*1000, -(squared-cap)*1000

    simplex_start = np.maximum(log_weights, simplex_floor)
    simplex_start /= simplex_start.sum()
    simplex_result = minimize(
        simplex, simplex_start, jac=True, method="SLSQP",
        bounds=[(simplex_floor, 1)]*92,
        constraints={"type": "eq", "fun": lambda weights: weights.sum()-1,
                     "jac": lambda weights: np.ones(92)},
        options={"maxiter": iterations, "ftol": 1e-13, "disp": False})
    simplex_weights = np.maximum(simplex_result.x, simplex_floor)
    simplex_weights /= simplex_weights.sum()
    raw = [
        ("broader-log", log_weights, log_result),
        ("positive-simplex", simplex_weights, simplex_result),
        ("simplex-original-half-blend", (simplex_weights+start)/2, simplex_result),
    ]
    result = []
    for name, weights, optimizer in raw:
        support, checked = exact_support(original, kernel, point, weights)
        floating_energy, _ = old_numerical.float_energy(edges, weights, anchors)
        result.append((support, checked, {
            "strategy": name, "floating_optimizer_NOT_proof": True,
            "success": bool(optimizer.success), "message": str(optimizer.message),
            "iterations": int(optimizer.nit),
            "floating_normalized_point_energy_NOT_proof": floating_energy,
            "log_spread": log_spread, "simplex_floor": simplex_floor,
        }))
    return result
