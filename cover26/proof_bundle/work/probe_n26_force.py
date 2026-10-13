"""Untrusted SLSQP proposals for the N26 exact rod-force checker."""

import argparse
from fractions import Fraction as F
import json
from math import pi
from pathlib import Path
import time

import numpy as np
from scipy.optimize import minimize

from audit_prefix_origin import OriginReference
from n26_force import CAPS, D, U, angular_domain, load_trig, rationalize, rod_graph, rootbox


WORK = Path(__file__).resolve().parent


class Solver:
    def __init__(self, spec):
        self.spec, self.b = spec, spec["B"]
        self.vertices, edges = rod_graph(spec)
        self.edges = edges
        self.E = np.array(edges)
        self.incidence = np.zeros((len(edges), self.vertices - 1))
        laplacian = np.zeros((self.vertices, self.vertices))
        for k, (u, v) in enumerate(edges):
            if u:
                self.incidence[k, u - 1] = 1
            if v:
                self.incidence[k, v - 1] = -1
            laplacian[u, u] += 1
            laplacian[v, v] += 1
            laplacian[u, v] -= 1
            laplacian[v, u] -= 1
        self.harmonic = -np.linalg.solve(laplacian[self.b:, self.b:],
                                        laplacian[self.b:, :self.b])
        self.arcs = load_trig()[0]

    def solve(self, lower, upper, maxiter=120):
        b, count = self.b, len(self.edges)
        nvar = 2 * (self.vertices - 1) + 1
        aa, bb = [], []
        for lo, hi in zip(lower, upper):
            a, c = self.arcs.arc_halfplane(lo, hi)
            aa.append(a)
            bb.append(c)
        aa, bb = np.array(aa, float) / self.arcs.QA, np.array(bb, float) / self.arcs.QB

        def values(x):
            z = np.vstack(([1., 0.], x[:-1].reshape(-1, 2)))
            ds = z[self.E[:, 0]] - z[self.E[:, 1]]
            return z, ds, np.linalg.norm(ds, axis=1), np.linalg.norm(z[1:b], axis=1)

        def constraint(x):
            z, ds, lengths, anchor_norms = values(x)
            return np.r_[x[-1] - lengths, np.einsum("ij,ij->i", aa, z[1:b]) - bb,
                         1 - anchor_norms]

        def jacobian(x):
            z, ds, lengths, anchor_norms = values(x)
            directions = ds / np.maximum(lengths[:, None], 1e-15)
            jac = np.zeros((count + 2 * (b - 1), nvar))
            jac[:count, -1] = 1
            jac[:count, :-1] = -(self.incidence[:, :, None] * directions[:, None, :]).reshape(count, -1)
            for i in range(b - 1):
                jac[count + i, 2 * i:2 * i + 2] = aa[i]
                jac[count + b - 1 + i, 2 * i:2 * i + 2] = -z[i + 1] / max(anchor_norms[i], 1e-15)
            return jac

        angles = np.r_[0., [2 * pi * float((lo + hi) / 2) for lo, hi in zip(lower, upper)]]
        anchors = np.c_[np.cos(angles), np.sin(angles)]
        z = np.vstack((anchors, self.harmonic @ anchors))
        x0 = np.r_[z[1:].ravel(), np.max(np.linalg.norm(z[self.E[:, 0]] - z[self.E[:, 1]], axis=1)) + .02]
        objective = np.zeros(nvar)
        objective[-1] = 1
        start = time.monotonic()
        result = minimize(lambda x: x[-1], x0, jac=lambda x: objective,
                          constraints={"type": "ineq", "fun": constraint, "jac": jacobian},
                          method="SLSQP", options={"ftol": 1e-11, "maxiter": maxiter, "disp": False})
        z, ds, lengths, anchor_norms = values(result.x)
        status = {"floating_success": bool(result.success), "proposed_radius": float(result.fun),
                  "iterations": int(result.nit), "constraint_minimum": float(np.min(constraint(result.x))),
                  "seconds": time.monotonic() - start,
                  "anchor_norms_proposal": anchor_norms.tolist()}
        cert, exact = None, None
        if hasattr(result, "multipliers"):
            multipliers = result.multipliers
            lam = multipliers[count:count + b - 1]
            support = multipliers[count + b - 1:, None] * z[1:b] / np.maximum(anchor_norms[:, None], 1e-15)
            flow = multipliers[:count, None] * ds / np.maximum(lengths[:, None], 1e-15)
            cert, exact = rationalize(self.spec, lower, upper, lam, support, flow, self.arcs)
        status["positive_exact_force_certificate_proposed"] = cert is not None
        status["exact_reconstruction_result"] = exact
        return cert, status


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source = json.loads((WORK.parent / "outputs/n26-current-cover-transport-frontier-v1.json").read_text())
    rows = [row for row in source["pending_states"] if row["B"] == 14]
    diagnostic = json.loads((WORK / "n26-B14-adaptive-area-proposals-v1.json").read_text())
    terminal_prefix = diagnostic["events"][-1]["prefix"]
    reference = OriginReference(26, 14, "dfs", caps=CAPS, scale=D)
    terminal = reference.resolve(tuple(terminal_prefix))
    rows.append({"B": 14, **reference.entry(tuple(terminal_prefix), terminal, [])})
    results = []
    for row in rows:
        spec = {"N": 26, "B": row["B"], "next": row["next"], "faces": row["faces"]}
        mat = angular_domain(spec)
        lower, upper = rootbox(mat)
        cert, status = Solver(spec).solve(lower, upper)
        record = {"prefix": row["prefix"], "spec": spec,
                  "lower": list(map(str, lower)), "upper": list(map(str, upper)),
                  "certificate_proposal": cert, "status": status}
        results.append(record)
        print(json.dumps({"prefix": row["prefix"], **status}), flush=True)
    args.output.write_text(json.dumps({"verified": False, "results": results,
                                       "global_optimality_proved": False}, indent=2) + "\n")


if __name__ == "__main__":
    main()
