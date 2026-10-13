"""Unaccepted fixed-anchor dual equilibration; only exact arc checks can pay."""

import argparse
from fractions import Fraction as F
import json
from math import pi
from pathlib import Path

import numpy as np
from scipy.optimize import lsq_linear

from n26_force import spanning_tree
from n26_sharp_radius_constraints import cap_gate, constraint_matrix
import n26_correlated_arc_force as exact_force
import probe_direct_arc_force as fixed
from probe_correlated_arc_force import CorrelatedArcSolver
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import local_path, sha


def polish(solver, lower, upper, matrix, radius):
    lower, upper = list(map(F, lower)), list(map(F, upper))
    original_minimize = fixed.minimize
    captured = []

    def capture(*args, **kwargs):
        value = original_minimize(*args, **kwargs)
        captured.append(value)
        return value

    fixed.minimize = capture
    try:
        _, status = solver.solve_correlated(lower, upper, matrix, radius)
    finally:
        fixed.minimize = original_minimize
    result = captured[-1]
    turns = np.r_[0., [float((F(a) + F(b)) / 2) for a, b in zip(lower, upper)]]
    anchors = np.c_[np.cos(2 * pi * turns), np.sin(2 * pi * turns)]
    points = np.vstack((anchors, result.x[:-1].reshape(-1, 2)))
    ds = points[solver.E[:, 0]] - points[solver.E[:, 1]]
    lengths = np.linalg.norm(ds, axis=1)
    directions = ds / np.maximum(lengths[:, None], 1e-15)
    incidence = solver.incidence[:, solver.b - 1:]
    raw_weights = result.multipliers
    records = []
    for tolerance in (1e-9, 1e-8, 1e-7):
        selected = np.where((max(lengths) - lengths < tolerance) | (raw_weights > 1e-9))[0]
        equilibrium = (incidence[selected, :, None] * directions[selected, None, :]).reshape(len(selected), -1).T
        system = np.vstack((equilibrium, np.ones((1, len(selected)))))
        target = np.r_[np.zeros(equilibrium.shape[0]), 1.]
        balanced = lsq_linear(system, target, bounds=(0., np.inf), tol=1e-14, max_iter=500)
        weights = np.zeros(len(solver.edges))
        weights[selected] = balanced.x
        flow = weights[:, None] * directions
        loads = np.zeros((solver.b, 2))
        for (u, v), row in zip(solver.edges, flow):
            if u < solver.b:
                loads[u] += row
            if v < solver.b:
                loads[v] -= row
        q = 10**30
        chords = spanning_tree(solver.vertices, solver.edges)[2]
        base = {"q": q, "g": [round(float(x) * q) for row in loads[1:] for x in row],
                "f": [round(float(flow[k][d]) * q) for k in chords for d in range(2)]}
        cert, diagnostic = solver.difference_dual(lower, upper, matrix, base)
        if cert is None:
            continue
        check = exact_force.force_check(solver.spec, lower, upper, matrix, cert, solver.arcs)
        margin = F(check["required_radius_lower"]) - radius
        records.append({"active_tolerance": tolerance, "active_edges": len(selected),
                        "floating_equilibrium_maximum_residual": float(np.max(np.abs(system @ balanced.x - target))),
                        "exact_whole_box_force_margin": str(margin), "certificate_proposal": cert})
    return status, records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=4)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.source)
    cap_report, _ = bound(args.caps)
    source = read(args.source / "CERTIFICATE.json")
    cap = read(args.caps / "CERTIFICATE.json")
    matrix = read(args.caps / "MATRIX.json")
    radius = F(cap["radius_upper"])
    pending = read(args.source / "PENDING-ANGLES.json")
    pending.sort(key=lambda row: sum((F(b) - F(a))**2 for a, b in zip(
        row["sharp_lower"], row["sharp_upper"])))
    solver = CorrelatedArcSolver(source["spec"])
    source_manifest = read(args.source / "MANIFEST.json")
    caps = cap_gate(radius, cap, solver.arcs)[0]
    if (sha(local_path(source_manifest["sources"]["caps"]) / "VERIFIED.json") != sha(args.caps / "VERIFIED.json")
            or constraint_matrix(source["spec"], caps)[0] != matrix):
        raise ValueError("polished candidate diagnostics changed its source cap or complete matrix")
    records = []
    for row in pending[:args.limit]:
        status, candidates = polish(solver, row["sharp_lower"], row["sharp_upper"], matrix, radius)
        best = max((F(candidate["exact_whole_box_force_margin"]) for candidate in candidates), default=None)
        records.append({"index": row["index"], "sharp_lower": row["sharp_lower"],
                        "sharp_upper": row["sharp_upper"], "raw_status": status, "polished_candidates": candidates})
        print(json.dumps({"verified": False, "index": row["index"],
                          "best_exact_whole_box_force_margin": float(best) if best is not None else None,
                          "proposed_paid": best is not None and best > 0}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-polished-fixed-anchor-force-diagnostics-v1", "verified": False,
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "cap_acceptance_sha256": sha(args.caps / "VERIFIED.json"), "results": records,
        "all_numerical_objectives_and_equilibrium_residuals_are_not_proofs": True,
        "independent_current_tree_acceptance_still_required": True, "global_optimality_proved": False},
        separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
