"""Unaccepted free-angle rod search on retained sharp candidate boxes."""

import argparse
from fractions import Fraction as F
import json
from math import pi
from pathlib import Path
import time

import numpy as np
from scipy.optimize import minimize

from n26_force import spanning_tree
from n26_sharp_radius_constraints import SCALE, constraint_matrix
from probe_correlated_arc_force import CorrelatedArcSolver
import verify_leaf_pinned_candidate_angles as leaf


class JointAngleSolver(CorrelatedArcSolver):
    def solve_joint(self, lower, upper, matrix, radius, maxiter=220):
        b, edge_count, nangle = self.b, len(self.edges), self.b - 1
        free_count = self.vertices - b
        incidence = self.incidence[:, nangle:]
        pairs = [(i, j) for i in range(b) for j in range(b) if i != j]
        sources, targets = np.array(pairs).T
        bounds = np.array([float(F(matrix[i][j], SCALE)) for i, j in pairs])
        angular_jacobian = np.zeros((len(pairs), nangle))
        for k, (i, j) in enumerate(pairs):
            if i:
                angular_jacobian[k, i - 1] += 1
            if j:
                angular_jacobian[k, j - 1] -= 1

        def values(x):
            turns = np.r_[0., x[:nangle]]
            angles = 2 * pi * turns
            anchors = np.c_[np.cos(angles), np.sin(angles)]
            tangent = 2 * pi * np.c_[-np.sin(angles), np.cos(angles)]
            points = np.vstack((anchors, x[nangle:-1].reshape(-1, 2)))
            ds = points[self.E[:, 0]] - points[self.E[:, 1]]
            lengths = np.linalg.norm(ds, axis=1)
            return turns, points, ds, lengths, tangent

        def constraints(x):
            turns, points, ds, lengths, tangent = values(x)
            return np.r_[x[-1] - lengths, bounds - turns[targets] + turns[sources]]

        def jacobian(x):
            turns, points, ds, lengths, tangent = values(x)
            directions = ds / np.maximum(lengths[:, None], 1e-15)
            jac = np.zeros((edge_count + len(pairs), len(x)))
            jac[:edge_count, -1] = 1
            jac[:edge_count, nangle:-1] = -(incidence[:, :, None] * directions[:, None, :]).reshape(edge_count, -1)
            for k, (u, v) in enumerate(self.edges):
                if 0 < u < b:
                    jac[k, u - 1] -= np.dot(directions[k], tangent[u])
                if 0 < v < b:
                    jac[k, v - 1] += np.dot(directions[k], tangent[v])
            jac[edge_count:, :nangle] = angular_jacobian
            return jac

        midpoint = np.array([float((a + c) / 2) for a, c in zip(lower, upper)])
        angles = 2 * pi * np.r_[0., midpoint]
        anchors = np.c_[np.cos(angles), np.sin(angles)]
        free = self.harmonic @ anchors
        points = np.vstack((anchors, free))
        initial_radius = np.max(np.linalg.norm(points[self.E[:, 0]] - points[self.E[:, 1]], axis=1)) + .02
        x0 = np.r_[midpoint, free.ravel(), initial_radius]
        objective = np.zeros(len(x0))
        objective[-1] = 1
        start = time.monotonic()
        result = minimize(
            lambda x: x[-1], x0, jac=lambda x: objective,
            bounds=[(float(a), float(c)) for a, c in zip(lower, upper)]
                   + [(-1.2, 1.2)] * (2 * free_count) + [(0., None)],
            constraints={"type": "ineq", "fun": constraints, "jac": jacobian},
            method="SLSQP", options={"ftol": 1e-12, "maxiter": maxiter, "disp": False})
        turns, points, ds, lengths, tangent = values(result.x)
        record = {
            "floating_success": bool(result.success), "iterations": int(result.nit),
            "floating_joint_radius": float(result.fun),
            "floating_constraint_minimum": float(np.min(constraints(result.x))),
            "seconds": time.monotonic() - start, "joint_angles": turns[1:].tolist(),
            "joint_center_coordinates": points[b:b + self.spec["next"]].tolist(),
            "joint_internal_witness_coordinates": points[b + self.spec["next"]:].tolist(),
            "potential_improvement_requires_independent_continuous_cover_certificate":
                bool(result.fun < float(radius) - 1e-8 and np.min(constraints(result.x)) >= -1e-8),
            "proposed_paid_radius_conditional_force": False}
        if not hasattr(result, "multipliers"):
            return record
        flow = result.multipliers[:edge_count, None] * ds / np.maximum(lengths[:, None], 1e-15)
        loads = np.zeros((b, 2))
        for (u, v), row in zip(self.edges, flow):
            if u < b:
                loads[u] += row
            if v < b:
                loads[v] -= row
        q = 10**30
        chords = spanning_tree(self.vertices, self.edges)[2]
        base = {"q": q, "g": [round(float(x) * q) for row in loads[1:] for x in row],
                "f": [round(float(flow[k][d]) * q) for k in chords for d in range(2)]}
        try:
            cert, diagnostic = self.difference_dual(lower, upper, matrix, base)
        except ValueError as error:
            record["force_proposal_failure"] = str(error)
        else:
            record.update(diagnostic)
            if cert is not None and F(diagnostic["exact_correlated_bound"]["required_radius_lower"]) > radius:
                record["proposed_paid_radius_conditional_force"] = True
                record["force_certificate_proposal"] = cert
        return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checks", type=int, default=6)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, inventory = leaf.bound(args.source)
    cap_report, files = leaf.bound(args.caps)
    inventory.extend(files)
    source = json.loads((args.source / "CERTIFICATE.json").read_text())
    cap = json.loads((args.caps / "CERTIFICATE.json").read_text())
    if (accepted["source_acceptance_sha256"]["sharp_caps"] != leaf.sha(args.caps / "VERIFIED.json")
            or source["source_acceptance_sha256"] != accepted["source_acceptance_sha256"]):
        raise ValueError("joint discovery changed its accepted source or necessary cap interface")
    matrix, derivation = constraint_matrix(source["spec"], list(map(int, cap["caps"])))
    if matrix != json.loads((args.caps / "MATRIX.json").read_text()):
        raise ValueError("joint discovery matrix belongs to a different graph")
    radius = F(cap["radius_upper"])
    pending = json.loads((args.source / "PENDING-ANGLES.json").read_text())
    pending.sort(key=lambda row: max(F(b) - F(a) for a, b in zip(row["sharp_lower"], row["sharp_upper"])), reverse=True)
    solver = JointAngleSolver(source["spec"])
    results = []
    hashes = {str(path): leaf.sha(path) for path in inventory}
    for row in pending[:args.checks]:
        result = solver.solve_joint(list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])), matrix, radius)
        results.append({"index": row["index"], **result})
        print(json.dumps({key: result[key] for key in (
            "floating_success", "floating_joint_radius", "floating_constraint_minimum",
            "potential_improvement_requires_independent_continuous_cover_certificate",
            "proposed_paid_radius_conditional_force")}, separators=(",", ":")), flush=True)
    if any(leaf.sha(path) != digest for path, digest in hashes.items()):
        raise ValueError("joint discovery source bytes changed")
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-free-angle-rod-discovery-v1", "verified": False,
        "source_acceptance_sha256": leaf.sha(args.source / "VERIFIED.json"),
        "source_certificate_sha256": leaf.sha(args.source / "CERTIFICATE.json"),
        "spec": source["spec"], "radius_scope": "same-root-Rstar", "results": results,
        "new_angular_leaf_semantics_and_full_chain_acceptance_pending": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
