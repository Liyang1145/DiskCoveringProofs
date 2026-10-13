"""Numerical proposals from a fixed-anchor convex rod problem, exact replayed."""

from fractions import Fraction as F
from math import pi
import time

import numpy as np
from scipy.optimize import minimize

from n26_force import spanning_tree
from n26_direct_arc_force import force_check
from probe_n26_force import Solver


class DirectArcSolver(Solver):
    def solve_sharp(self, lower, upper, radius_upper, maxiter=180):
        b, count = self.b, len(self.edges)
        nfree = self.vertices - b
        angles = np.r_[0., [2 * pi * float((lo + hi) / 2) for lo, hi in zip(lower, upper)]]
        anchors = np.c_[np.cos(angles), np.sin(angles)]
        incidence = np.zeros((count, nfree))
        for k, (u, v) in enumerate(self.edges):
            if u >= b:
                incidence[k, u - b] = 1
            if v >= b:
                incidence[k, v - b] = -1

        def values(x):
            z = np.vstack((anchors, x[:-1].reshape(-1, 2)))
            ds = z[self.E[:, 0]] - z[self.E[:, 1]]
            return z, ds, np.linalg.norm(ds, axis=1)

        def constraint(x):
            return x[-1] - values(x)[2]

        def jacobian(x):
            z, ds, lengths = values(x)
            directions = ds / np.maximum(lengths[:, None], 1e-15)
            jac = np.zeros((count, 2 * nfree + 1))
            jac[:, -1] = 1
            jac[:, :-1] = -(incidence[:, :, None] * directions[:, None, :]).reshape(count, -1)
            return jac

        initial = self.harmonic @ anchors
        z0 = np.vstack((anchors, initial))
        x0 = np.r_[initial.ravel(), np.max(np.linalg.norm(z0[self.E[:, 0]] - z0[self.E[:, 1]], axis=1)) + .02]
        objective = np.zeros(2 * nfree + 1)
        objective[-1] = 1
        start = time.monotonic()
        result = minimize(lambda x: x[-1], x0, jac=lambda x: objective,
                          constraints={"type": "ineq", "fun": constraint, "jac": jacobian},
                          method="SLSQP", options={"ftol": 1e-13, "maxiter": maxiter, "disp": False})
        z, ds, lengths = values(result.x)
        status = {
            "floating_success": bool(result.success), "proposed_radius": float(result.fun),
            "constraint_minimum": float(np.min(constraint(result.x))),
            "anchor_norms_proposal": [1.] * (b - 1), "seconds": time.monotonic() - start,
        }
        cert, last, influence = None, None, [1.] * (b - 1)
        self.last_direct_candidate = None
        if hasattr(result, "multipliers"):
            flow = result.multipliers[:, None] * ds / np.maximum(lengths[:, None], 1e-15)
            loads = np.zeros((b, 2))
            for (u, v), f in zip(self.edges, flow):
                if u < b:
                    loads[u] += f
                if v < b:
                    loads[v] -= f
            influence = np.linalg.norm(loads[1:], axis=1).tolist()
            _, _, chords = spanning_tree(self.vertices, self.edges)
            for q in (10**8, 10**12, 10**18, 10**30):
                candidate = {
                    "q": q, "g": [round(float(x) * q) for row in loads[1:] for x in row],
                    "f": [round(float(flow[k][d]) * q) for k in chords for d in range(2)],
                }
                self.last_direct_candidate = candidate
                last = force_check(self.spec, lower, upper, candidate, self.arcs)
                if F(last["required_radius_lower"]) > radius_upper:
                    cert = candidate
                    break
        status["exact_candidate_bound"] = last
        status["anchor_force_norm_proposal"] = influence
        return cert, status
