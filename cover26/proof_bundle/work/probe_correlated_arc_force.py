"""Untrusted LP dual proposals; each result is paid by exact arithmetic."""

from fractions import Fraction as F
from math import pi

import numpy as np
from scipy.optimize import linprog

from n26_correlated_arc_force import force_check
from n26_sharp_radius_constraints import SCALE
from probe_direct_arc_force import DirectArcSolver


class CorrelatedArcSolver(DirectArcSolver):
    def difference_dual(self, lower, upper, matrix, base):
        b, q = self.b, base["q"]
        lo, hi = np.r_[0., list(map(float, lower))], np.r_[0., list(map(float, upper))]
        middle = (lo + hi) / 2
        pairs = [(i, j) for i in range(b) for j in range(b) if i != j]
        incidence = np.zeros((b - 1, len(pairs)))
        costs = []
        for k, (i, j) in enumerate(pairs):
            if i:
                incidence[i - 1, k] += 1
            if j:
                incidence[j - 1, k] -= 1
            costs.append(min(float(F(matrix[i][j], SCALE)), hi[j] - lo[i]) + middle[i] - middle[j])
        loads = np.array(base["g"], dtype=float).reshape(-1, 2) / q
        derivative = 2 * pi * (-loads[:, 0] * np.sin(2 * pi * middle[1:])
                              + loads[:, 1] * np.cos(2 * pi * middle[1:]))
        residual = -np.eye(b - 1)
        result = linprog(
            np.r_[costs, (hi[1:] - lo[1:]) / 2],
            A_ub=np.r_[np.c_[incidence, residual], np.c_[-incidence, residual]],
            b_ub=np.r_[derivative, -derivative], bounds=(0, None), method="highs")
        if not result.success:
            return None, {"floating_difference_LP_success": False}
        mu = [[i, j, str(round(float(value) * q))]
              for (i, j), value in zip(pairs, result.x[:len(pairs)]) if round(float(value) * q) > 0]
        certificate = {**base, "mu": mu}
        exact = force_check(self.spec, lower, upper, matrix, certificate, self.arcs)
        return certificate, {
            "floating_difference_LP_success": True,
            "proposed_difference_dual_terms": len(mu),
            "exact_correlated_bound": exact,
        }

    def solve_correlated(self, lower, upper, matrix, radius_upper):
        certificate, status = self.solve_sharp(lower, upper, radius_upper)
        if certificate is not None:
            return {"kind": "SHARP_FORCE", "cert": certificate}, status
        base = getattr(self, "last_direct_candidate", None)
        if base is None:
            return None, status
        certificate, dual_status = self.difference_dual(lower, upper, matrix, base)
        status.update(dual_status)
        if certificate is not None and F(dual_status["exact_correlated_bound"]["required_radius_lower"]) > radius_upper:
            return {"kind": "SHARP_CORRELATED_FORCE", "cert": certificate}, status
        return None, status
